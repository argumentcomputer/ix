# PLAN — `Toplevel.compile_correct` closure

**Status**: Branch `ap/aiur-compiler`. Build green. **8 reachable sorries from `compile_correct`** (Invariant 1 satisfied; zero orphans). Layout chain sorry-free except `dataTypeFlatSize_bound_saturation_wf` (#5sat: 1 bundled sorry covering 4 BLOCKED sub-leaves; sub-leaf 1 partially decomposed 2026-05-04 — see "Sub-leaf decomposition" entry below for `dataTypeFlatSizeBound_mono_source_chain`).

2026-05-04 — `Toplevel.compile_correct`'s body carries 2 granular sub-sorries (down from 3 — `BLOCKED-CtorAgrees-index` closed 2026-05-04 via the new entry-restricted variant):
- `hCtorPreserved`: CLOSED end-to-end (3-step chain `checkAndSimplify_preserves_ctor_kind_fwd` → `concretizeBuild_preserves_ctor_kind_at_entry_fwd` → `step4Lower_preserves_ctor_kind_fwd`).
- `hDeclsR`: CLOSED for both `Decls.CtorPreserved` and `Decls.FnNamesAgree` clauses (function variant uses `concretizeBuild_preserves_function_inputs_at_entry_fwd` + `step4Lower_function_explicit` + inline `mapM_first_proj`).
- `hCtorAgreesAll`: index-half CLOSED (uses new `PhaseA2.concretizeBuild_at_typed_ctor_at_entry_fwd` in CtorKind.lean — single-key entry-restricted variant of `_explicit_general` that uses `ConcretizeUniqueNames` in lieu of universal `params_empty`). Flat-size half (`BLOCKED-CtorAgrees-flat-size`) remains.
- `hApplyGlobalReach`: untouched (`BLOCKED-ConcreteApplyGlobalReach`, 1 sorry; awaiting `Concrete.MonoCtorReachBody` mirror plant).

So `compile_correct`'s sub-sorry count is 6 → 2 — the residuals are the flat-size sub-leaf and the concrete-side `applyGlobal` mirror.

Sig-defects from the audit closed 2026-05-04 — each formerly hoisted-as-False premise now has a sig that admits a true witness. See "Sig amendments 2026-05-04 — defect closures" at the bottom.

**Reachable sorry inventory (9)**:

| # | Location | Theorem | Category |
|---|---|---|---|
| 1.C | ValueEqFlatten:579 | `MonoCtorReachBody.interp_MonoCtorReach` | A.5 keystone leaf (~1100 LoC) |
| 2 | LowerSoundControl:58 | `Function_body_preservation_succ_fuel` | E.2 |
| 3 | TermRefsDtBridge:163 | `concretize_preserves_TermRefsDt` (bridge discharge sub-leaf — the relocated `concretizeBuild_preserves_TermRefsDt` body is closed) | E.5 |
| 5sat | Layout:~1733 | `dataTypeFlatSize_bound_saturation_wf` | dt-level bound-saturation (4 BLOCKED sub-leaves, bundled) |
| 8 | CompilerProgress:3639 | `sizeBoundOk_entry` | C.2 |
| 9 | CompilerProgress:3679 | `function_compile_progress_entry` | C.2 |
| 11* | StructCompatible:1599 | `compile_ok_implies_struct_compatible_of_entry` (consumer site for hoisted #11 obligations) | A.4-trade (hoisted) |
| 12 | Simulation:413 | `step_R_preservation_applyGlobal` | B.2 (heart) |
| 15 | CompilerCorrect:186 | `compile_correct` (carries 2 granular sub-sorries: `hCtorAgreesAll`-flat-size, `hApplyGlobalReach`) | top-level |

## Per-sorry rigorous closure plans

Each plan below is RIGOROUS: another agent should be able to execute the closure path without re-discovering structure. Theorem references list `(File.lean:Line)`. Wherever a step says "apply X", `X` is a real (already-defined) theorem in the repo unless flagged `NEW`. All BLOCKED tags below name leaves currently planted in source.

### Sorry #1.C — `MonoCtorReachBody.interp_MonoCtorReach` (`ValueEqFlatten.lean:534`)

**Sig**:
```
theorem interp_MonoCtorReach
    {decls} {concDecls} (_hCtorPreserved : Decls.CtorPreserved decls concDecls)
    (fuel : Nat) (bindings : Bindings) (t : Source.Term) (st : EvalState)
    (_hbindReach : BindingsMonoCtorReach decls concDecls bindings)
    (v : Value) (st' : EvalState)
    (_heval : Source.Eval.interp decls fuel bindings t st = .ok (v, st')) :
    Value.MonoCtorReach decls concDecls v
```

**Closure path**: Case-split on `Source.Term` constructor (~40 arms — see file's docstring at `ValueEqFlatten.lean:391-438` for per-arm specifics). The bulk of the FnFree mutual-block parallel. Direct-leaf arms produce `MonoCtorReach.{unit, field, fn, pointer, tuple, array}`. Composite arms recurse via `evalList_MonoCtorReach` (#1.D, closed) / `evalMatchCases_MonoCtorReach` (#1.E, closed) / `applyGlobal_MonoCtorReach` (#1.A, closed) / `applyLocal_MonoCtorReach` (#1.B, closed), passing `interp_MonoCtorReach` itself as `_hInterpReach` (mutual self-reference). Then build via `Value.MonoCtorReach.{tuple, array, ctor}` from per-element witnesses. `.let` / `.match` arms need sub-helper `matchPattern_BindingsMonoCtorReach` (mirror of `matchPattern_bindingsFnFree` at `ConcretizeSound/FnFree.lean:1182`). **~1100 LoC**.

**Existing infrastructure planted in source** (`ValueEqFlatten.lean:316-340`):
* `MonoCtorReachBody.BindingsMonoCtorReach`: per-binding `MonoCtorReach` predicate.
* `BindingsMonoCtorReach.{nil, cons, append, find?_MonoCtorReach}`: helpers (closed).
* Public `runFunction_preserves_MonoCtorReach` body (line 525): closed via dispatch to `applyGlobal_MonoCtorReach`.
* #1.A/B/D/E closed via hoisted `_hInterpReach` premise — discharged here by passing `interp_MonoCtorReach` itself (mutual self-reference).

**Existing infrastructure to reuse**:
- `Concrete.Eval.runFunction_preserves_FnFree` + `FnFreeBody` mutual block (`ConcretizeSound/FnFree.lean:20-1443`) — line-for-line template.
- `Value.MonoCtorReach` predicate (`ValueEqFlatten.lean:131`) + projections `tuple_inv` / `array_inv` / `ctor_src` / `ctor_conc` / `ctor_args` (`ValueEqFlatten.lean:150-181`).
- `Decls.CtorPreserved` predicate (`ValueEqFlatten.lean:249`).

**Dependencies on other sorries**: None.

**LoC estimate**: ~1100 LoC.

**Risk factors**:
- `Source.Eval.applyGlobal` and `Concrete.Eval.applyGlobal` use slightly different runtime layouts; per-arm proofs are not verbatim copies.
- `termination_by` will need cross-checking with `SourceEval.lean` mutual termination ordering.
- The `.set` arm needs `Array.mem_set!` lemma.
- The `.load` arm reads from the EvalState store — may need a `StoreMonoCtorReach` invariant preserved across `.store`. Plant as sub-helper if needed.
- `matchPattern_BindingsMonoCtorReach` sub-helper (~50 LoC) needed for `.let`/`.match` arms.

---

### Sorry #2 — `Function_body_preservation_succ_fuel` (`LowerSoundControl.lean:58`)

**Sig**:
```
private theorem Function_body_preservation_succ_fuel
    {cd : Concrete.Decls} {bytecode : Bytecode.Toplevel}
    {preNameMap : Std.HashMap Global Bytecode.FunIdx}
    {decls : Source.Decls} {lm : LayoutMap}
    (_hbc : cd.toBytecode = .ok (bytecode, preNameMap))
    (_hlm : cd.layoutMap = .ok lm)
    (name : Global) (f : Concrete.Function)
    (_hname : cd.getByKey name = some (.function f))
    (funIdx : Bytecode.FunIdx) (_hfi : preNameMap[name]? = some funIdx)
    (args : List Value) (io₀ : IOBuffer) (fuel' : Nat) (retTyp : Typ) :
    InterpResultEq decls (fun g => preNameMap[g]?) retTyp
      (Concrete.Eval.runFunction cd name args io₀ (fuel'+1))
      (Bytecode.Eval.runFunction bytecode funIdx
        (Flatten.args decls (fun g => preNameMap[g]?) args) io₀ (fuel'+1))
```

**Closure category**: Per-block dispatch + per-arm `toIndex_preservation_core_extended` cascade.

**Closure path** (precise, step-by-step):
1. **Reduce both runners to per-block evaluators**: `unfold Concrete.Eval.runFunction` on LHS to expose `Concrete.Eval.applyGlobal` then `Concrete.Eval.interpBlock` on `f.body` with empty bindings + `args` populated by `f.inputs.zip args`. `unfold Bytecode.Eval.runFunction` on RHS to expose the `Bytecode.Eval.interpFunction` over `bytecode.functions[funIdx]`.
2. **Extract bytecode function from cd**: apply `toBytecode_function_extract _hbc _hname _hfi` (already F=0 in `LowerShared.lean`) to obtain `bf : Bytecode.Function` with `bytecode.functions[funIdx] = bf` and `Concrete.Function.compile lm f = .ok (bf.body, lms)`.
3. **Establish input-bindings agreement**: invoke `inputs_foldlM_ok` (currently in Scratch.lean:1382; migrate to LowerShared.lean as part of closure) to produce `bindings_conc` matching `f.inputs.zip args` and `Bytecode` flat slot range agreement via `Flatten.args decls funcIdx args` width-bucket. Agreement comes from `typSize_ok_of_refClosed_lm` (LowerShared.lean) per input.
4. **Dispatch to body bridge**: invoke `toIndex_preservation_core_extended` (LowerSoundCore.lean) with witness package `{ hbc, hlm, hctxR := bindings agreement from (3), hStateR := init, hargsR := from (3) }`. This bridge handles all 25 source-term arms and recursively calls `Function_body_preservation_succ_fuel` at `fuel'` for `.app` arms (cross-recursion fuel decrement).
5. **`.app` arm cross-call**: when `toIndex_preservation_core_extended` hits the `.app` arm, it builds args via `flattenValue` per-input agreement and calls `Function_body_preservation_succ_fuel _hbc _hlm callee_g callee_f hcallee fc.idx hfi_callee args' io' fuel'-1 retTyp_callee`. Termination is on `fuel'`.
6. **Tail-position handling for `.match`/`.ret`/`Ctrl.matchContinue`/`Ctrl.return`/`Ctrl.yield`**: NEW `Block.compile_preservation` helper (~150 LoC), currently fused into the body. Plant as a separate F=1 theorem with documented arm-by-arm closure: each tail arm reduces to `toIndex_preservation_core_extended` on its scrutinee/value-position term, then constructs `Bytecode.Block.match`/`.return`/`.yield` to discharge.
7. **IO clause**: `Bytecode.Eval.runFunction` returns `(_, io_final)`; agreement comes from threading `IOBuffer.equiv` through every IO-touching arm (`.printChar`, etc.) — already F=0 in those arms of `toIndex_preservation_core_extended`.

**Existing infrastructure to reuse**:
- `toBytecode_function_extract` (`LowerShared.lean`) — F=0 cd-key → bytecode-function lookup.
- `toBytecode_layoutMap_ok` (`LowerShared.lean`) — derives `lm` from `_hbc` (already used at the caller `Function_body_preservation`, line 127).
- `toIndex_preservation_core_extended` (`LowerSoundCore.lean`) — main per-arm bridge, currently decomposed into 25 sub-sorries (status: 9 inherited + 4 arith + 10 u8/u32 + 4 IO + 1 store at F=0; 6 access arms F=1 needing `interp_preserves_ValueHasTyp`; `.app` arm at F=1, see Step 5).
- `inputs_foldlM_ok` (`Scratch.lean:1382`, mechanical migration) + `typSize_ok_of_refClosed_lm` (`LowerShared.lean`) for Step 3.
- `interp_preserves_ValueHasTyp` (`Scratch.lean:6000`, F=1 stub; see also `flattenValue_size_of_ValueHasTyp` `Scratch.lean:6473`, `flattenValue_slice_at_offset` `Scratch.lean:763`) — needed by the 6 access arms in `toIndex_preservation_core_extended`.

**Dependencies on other sorries**: Sorry #12 (`step_R_preservation_applyGlobal`, B.2) — the cross-call simulation provides the recursion handle for the `.app` arm at Step 5/6. Closure of #12 unblocks the `.app` arm.

**LoC estimate**: ~400 LoC for the headline body + per-block dispatch + tail handling, **plus** ~500-1000 LoC of `interp_preserves_ValueHasTyp` (separate piece, blocks 6 access arms inside `toIndex_preservation_core_extended`).

**Risk factors**:
- `interp_preserves_ValueHasTyp` is itself sorried (Scratch.lean:6000, F=1) — needs to be migrated upstream and closed first.
- `Block.compile_preservation` (Step 6) is currently un-extracted; the body-fusion in `toIndex_preservation_core_extended` may not cleanly factor without a sig refactor.
- Termination on `fuel'` may require explicit `termination_by` if Lean cannot infer the cross-call recursion structure; check by mirroring `Function_body_preservation_zero_fuel` at line 40 (which does have a termination annotation when called at higher fuel).

---

### Sorry #3 — `concretize_preserves_TermRefsDt` bridge (`ConcretizeSound/TermRefsDtBridge.lean:164`)

**Status (2026-05-04, third update)**: significant decomposition
completed.

* **Sig amendment 1**: `concretize_preserves_TermRefsDt` now takes
  `hdecls : t.mkDecls = .ok decls` so `mkDecls_ctor_companion` /
  `mkDecls_source_ctor_is_key` / `checkAndSimplify_src_dt_to_td` are in
  scope.
* **Sig amendment 2**: `Typed.Term.RefsDt`'s `.ref` arm tightened from
  the disjunctive `.dataType ∨ .constructor` premise to the
  ctor-only `∃ dt c, tds[g] = .constructor dt c` premise — the
  type-checker's `refLookup` (Check.lean:421) only emits `.ref` for
  constructors, so the dataType disjunct was structurally
  unreachable. Cascade: `rewriteTypedTerm_preserves_RefsDt`'s
  bridge premise + conclusion become single-disjunct;
  `concretizeBuild_preserves_TermRefsDt`'s `_hRefsBridge` parameter
  matches the tightened shape; `termToConcrete_preserves_RefsDt`'s
  bridge consumer at the `.ref` arm injects via `Or.inr hdt`.
* **Bridge body** (4-arm dispatch on `rewriteGlobal`):
  * **Arm B (`tArgs.nonempty + popNamespace = none`)** — CLOSED
    inline via `mkDecls_source_ctor_is_key` (ctor keys are always
    pushNamespace-formed).
  * **Arm A (`tArgs.isEmpty + ctor`)** — open BLOCKED-RefsDt-Bridge-A:
    needs `dt.params = []` for kind-fwd. Without an invariant
    linking `tArgs.size = dt.params.length` (cannot be added to
    `Typed.Term.RefsDt` since polymorphic mono-hit case breaks
    preservation through `rewriteTypedTerm`), the polymorphic dt at
    `g` case has `monoDecls.getByKey g = none` (srcStep skips poly).
  * **Arm C (mono-miss)** — open BLOCKED-RefsDt-Bridge-C-mono-miss:
    drain-reachability ("every body-ref `.ref g tArgs` has
    `(dt.name, tArgs)` populated in mono"), ~150 LoC structural lemma.
  * **Arm D (mono-hit)** — body fully wired except disjointness.
    Steps 1-8 close the materialization via `MonoShapeOk` +
    `FnMatchP` + `mkDecls_ctor_companion` + `mkDecls_source_ctor_is_key`.
    Step 9 (disjointness) BLOCKED-RefsDt-Bridge-D-disjoint: needs
    `ConcretizeUniqueNames` (closure pattern in `SizeBound.lean:1715-1820`
    using `concretizeName_singleton_ref_simple` + `hUnique`).

Net BLOCKED-tagged sub-sorry leaves remaining: 4 (A-ctor, C-mono-miss,
D-hDtNotKey, D-hFnNotKey). Decl-level sorry count unchanged at 1
(bundled). Recommended next sig amendment: take `hwf : WellFormed t`
to expose `ConcretizeUniqueNames` and close arm D's disjointness.

`concretizeBuild_preserves_TermRefsDt`'s body sorry (formerly at
`RefsDt.lean:1272`) is CLOSED via relocation + sig amendment. The
structural relocation moved 3 theorems out of `RefsDt.lean` (and
`Shapes.lean`) into a new downstream module
`Ix/Aiur/Proofs/ConcretizeSound/TermRefsDtBridge.lean` (downstream of
`Phase4` so `concretizeBuild_function_origin_with_body` from
`TypesNotFunction.lean` plus the kind-fwd lemmas from `CtorKind.lean`
are in scope). The remaining BLOCKED leaf — the bridge premise
`_hRefsBridge` discharged at the consumer `concretize_preserves_TermRefsDt`
— is now correctly localized at the call site where drain invariants
(`MonoHasDecl drained` / `StrongNewNameShape drained`) are derivable.

**Sig amendment 2026-05-04**: `concretizeBuild_preserves_TermRefsDt` now
takes a third hypothesis (`_hRefsBridge`):
```
theorem concretizeBuild_preserves_TermRefsDt
    {typedDecls : Typed.Decls} {mono : MonoMap}
    {newFunctions : Array Typed.Function} {newDataTypes : Array DataType}
    (htdsRef : Typed.Decls.TermRefsDt typedDecls)
    (hnfRef : ∀ f ∈ newFunctions, Typed.Term.RefsDt typedDecls f.body)
    (_hRefsBridge : ∀ g tArgs,
      ((∃ dt, typedDecls.getByKey g = some (.dataType dt)) ∨
       (∃ dt c, typedDecls.getByKey g = some (.constructor dt c))) →
      (∃ dt,
        (concretizeBuild typedDecls mono newFunctions newDataTypes).getByKey
          (rewriteGlobal typedDecls mono g tArgs) = some (.dataType dt)) ∨
      (∃ dt c,
        (concretizeBuild typedDecls mono newFunctions newDataTypes).getByKey
          (rewriteGlobal typedDecls mono g tArgs) = some (.constructor dt c))) :
    Typed.Decls.TermRefsDt (concretizeBuild typedDecls mono newFunctions newDataTypes)
```
Body: `concretizeBuild_function_origin_with_body` for origin inversion +
`rewriteTypedTerm_preserves_RefsDt` per arm with `_hRefsBridge` re-packed
as the universal bridge premise. **Body is sorry-free.**

**Remaining BLOCKED leaf**: bridge discharge at
`concretize_preserves_TermRefsDt` (`TermRefsDtBridge.lean:163`):
```
hRefsBridge : ∀ g tArgs,
  ((∃ dt, tds.getByKey g = some (.dataType dt)) ∨
   (∃ dt c, tds.getByKey g = some (.constructor dt c))) →
  (∃ dt, monoDecls.getByKey g' = some (.dataType dt)) ∨
  (∃ dt c, monoDecls.getByKey g' = some (.constructor dt c))
```
where `g' = rewriteGlobal tds drained.mono g tArgs` and
`monoDecls = concretizeBuild tds drained.mono drained.newFunctions
drained.newDataTypes`.

**Closure path** (precise, step-by-step) — 5-arm dispatch on `rewriteGlobal`
(documented inline in `TermRefsDtBridge.lean` post-amendment):

* **Arm A — `tArgs.isEmpty`**: rewriteGlobal returns `g`. Two sub-cases:
  * **A.dt. `tds[g] = .dataType dt`**: need `dt.params = []` to apply
    `concretizeBuild_preserves_dataType_kind_fwd` (CtorKind.lean:2156).
    Disjointness premises (`hDtCtorNotKey` / `hFnNotKey`) discharge
    via `concretize_drain_preserves_StrongNewNameShape` +
    `concretizeName_empty_args` (collisions ruled out via FullyMono
    or `ConcretizeUniqueNames`). BLOCKED-RefsDt-Bridge-poly-tArgsEmpty.
  * **A.ctor. `tds[g] = .constructor dt c`**: similar via
    `concretizeBuild_preserves_ctor_kind_fwd` (CtorKind.lean:422).
    BLOCKED-RefsDt-Bridge-poly-ctor-empty.
* **Arm B — `tArgs.nonempty + tds[g] = .function`**: bridge premise excludes function. Vacuous.
* **Arm C — `tArgs.nonempty + tds[g] = .constructor + popNamespace = none`**:
  ctor keys are formed as `dt.name.pushNamespace c.nameHead`, so popNamespace
  always returns `some`. Unreachable. BLOCKED-RefsDt-Bridge-popNamespace-none.
* **Arm D — `tArgs.nonempty + tds[g] = .constructor + popNamespace = some + mono-hit at (dt.name, tArgs)`**:
  rewriteGlobal returns `concDTName.pushNamespace ctorName`. Discharge via
  `concretizeBuild_at_newDt_ctor_name` (CtorKind.lean:2718) +
  `MonoShapeOk drained tds` (gives `newDt ∈ drained.newDataTypes`
  with shape `concDTName`'s constructors are `dt.constructors.map ...`).
  Disjointness via StrongNewNameShape + ConcretizeUniqueNames.
  BLOCKED-RefsDt-Bridge-monoHit (composition + disjointness + key-equality).
* **Arm E — `tArgs.nonempty + tds[g] = .constructor + popNamespace = some + mono-miss`**:
  rewriteGlobal returns `g` (poly ctor name) NOT in monoDecls. Discharge requires
  drain-reachability ("every body-ref `.ref g tArgs` site has `(dt.name, tArgs)`
  populated in mono"). BLOCKED-RefsDt-Bridge-mono-miss.
* **Arm F — `tArgs.nonempty + tds[g] = .dataType`**: rewriteGlobal falls
  through to `_ => g`. Same shape as A.dt under polymorphic dt.
  BLOCKED-RefsDt-Bridge-poly-dt-nonempty.

**The `dt.params = []` premise** in arms 1a, 1b, 2, 3, 4: holds when
`g` is a monomorphic source key. For polymorphic `g` (`dt.params != []`),
the typed body's `.ref g _ tArgs` cannot use `tArgs.isEmpty` (Aiur
type-checker pins `tArgs.size = dt.params.length`, see
`Check.lean:421`'s `refLookup`). So **arms 1a/1b under polymorphic `g`
are unreachable from typed bodies**, but the bridge is universally
quantified — proving they're vacuous requires structural reasoning.
The mono-miss case (arm 4) is similarly unreachable when the body
references `g`'s ctor: drain visits the template via the `.ref` site
(BodyAppRefToDt + drain reachability) so mono lookup hits.

**Existing infrastructure to reuse**:
- `concretizeBuild_preserves_{dataType,ctor}_kind_fwd` (CtorKind.lean) — identity arms.
- `concretizeBuild_at_newDt_ctor_name` (CtorKind.lean:2718) — mono-hit arm.
- `concretize_drain_preserves_StrongNewNameShape` (Shapes.lean) — drain invariant.
- `MonoHasDecl` / `MonoShapeOk` (MonoInvariants.lean / DrainInvariants.lean) — mono completeness.
- `Phase4.lean`'s `concretize_under_fullymono_preserves_{ctor,dataType}_kind_fwd` — similar pattern but under `FullyMonomorphic` (entry-restricted variant exists for ctor — Phase4.lean:577).

**Dependencies on other sorries**: None (all helpers F=0).

**LoC estimate**: ~250 LoC. Breakdown: ~40 LoC arm dispatch, ~60 LoC
arm 5 (mono-hit), ~100 LoC arms 1a/1b/2/3 (kind-fwd + disjointness from
StrongNewNameShape), ~50 LoC arm 4 (mono-miss reachability — the
hardest piece, requires a new "drain visits every reachable ctor"
helper or restriction to monomorphic typedDecls).

**Risk factors**:
- The polymorphic-source case (arm 4 mono-miss / arms 1a/1b/2/3 with
  `dt.params != []`) is structurally impossible under well-formed Aiur
  but requires either:
  (i) A new `WellFormed`-derived invariant
      `(_hAllDtsCtorsMono : ∀ g dt, tds.getByKey g = some (.dataType
      dt) → dt.params = []) ∧ ...` — but FALSE under polymorphic source
      (e.g., `Option<T>`), so cannot be a global hypothesis.
  (ii) A drain-reachability theorem: every body-referenced
      `(g_ctor, tArgs)` site has `(dt.name, tArgs)` populated in
      `drained.mono`. This is a substantial structural lemma about
      `concretizeDrain`'s collectCalls semantics; ~150 LoC of its own.
  (iii) A sig amendment to `Typed.Term.RefsDt` strengthening the
      `.ref` arm to require `dt.params = []` (effectively "no
      polymorphic dt/ctor at .ref sites"), which checkAndSimplify
      already enforces structurally per `refLookup`. This is the
      cleanest path — but would cascade through ~10 other consumers
      of `RefsDt`.
- Strategy (iii) is preferred for future closure.

---

### Sorry #5sat — `dataTypeFlatSize_bound_saturation_wf`

**Sig** (Layout.lean, after #5d's outer wrapper):
```
theorem dataTypeFlatSize_bound_saturation_wf
    {t : Source.Toplevel} {decls : Source.Decls}
    {typedDecls : Typed.Decls} {concDecls : Concrete.Decls}
    (_hwf : WellFormed t)
    (_hdecls : t.mkDecls = .ok decls)
    (_hts : t.checkAndSimplify = .ok typedDecls)
    (_hconc : typedDecls.concretize = .ok concDecls)
    (_hCtorArgsAlign : Source.Decls.DeclsAgreeOnDtFM decls concDecls)
    (_hKeysAlign : ∀ g' cd_dt,
       concDecls.getByKey g' = some (.dataType cd_dt) →
       cd_dt.name = g' ∧ ∃ dt, decls.getByKey g' = some (.dataType dt) ∧
         dt.params = [])
    {g : Global} {dt : DataType} {cd_dt : Concrete.DataType}
    (_hsrc : decls.getByKey g = some (.dataType dt))
    (_hcd : concDecls.getByKey g = some (.dataType cd_dt))
    (_hname : cd_dt.name = g)
    (_hparams : dt.params = []) :
    ∀ (n : Nat),
      Concrete.DataType.sizeBound concDecls (concDecls.size + 1) {} cd_dt = .ok n →
        dataTypeFlatSizeBound decls (decls.size + 1) {} dt = n
```

**Strategy (Option A)**: prove monotonicity for each side separately, bridge via `dataTypeFlatSizeBound_eq_sizeBound_wf` (#5d, closed) at a matched bound `M = max(decls.size + 1, concDecls.size + 1)`, then descend each side independently to its own top-level bound. Composition (Step 6):
* `dataTypeFlatSizeBound decls (decls.size + 1) {} dt`
* = `dataTypeFlatSizeBound decls M {} dt`            (mono-source)
* = `Concrete.DataType.sizeBound concDecls M {} cd_dt` (matched-bridge + bridge-perArgEq via #5d)
* = `Concrete.DataType.sizeBound concDecls (concDecls.size + 1) {} cd_dt` (mono-concrete reversed)
* = `.ok n` → `n` from `hsize`.

**Granular sub-leaves** (BUNDLED into single sorry inside lemma body; each leaf has a precise BLOCKED tag for resumption):

1. **BLOCKED-dtFlatSize-mono-source**: Source-side bound monotonicity. Statement (informal): `∀ b₁ b₂, b₁ ≥ decls.size + 1 → b₂ ≥ decls.size + 1 → dataTypeFlatSizeBound decls b₁ visited dt = dataTypeFlatSizeBound decls b₂ visited dt`.

   **Decomposition (2026-05-04)** — split into a CLOSED chaining helper plus a remaining analytical sub-leaf:
   - **`dataTypeFlatSizeBound_mono_source_chain`** (CLOSED, planted at `Layout.lean` just before `dataTypeFlatSize_bound_saturation_wf`, ~30 LoC): given a single-step mono hypothesis `hStep` at every intermediate bound between `b₁` and `b₂`, derives the any-bound `b₁ ≤ b₂` mono via induction on the gap `b₂ - b₁`. This factors the content-free arithmetic chaining out of the analytical claim.
   - **BLOCKED-dtFlatSize-mono-source-step**: discharge the `hStep` premise — the genuine analytical content. Statement: `∀ b ≥ decls.size + 1, dataTypeFlatSizeBound decls b visited dt = dataTypeFlatSizeBound decls (b+1) visited dt`. Closure: under acyclicity (rank witness `r : Global → Nat`) PLUS structural-depth bounds on constructor argTypes (every `t` in `decls.dataTypes[i].constructors[j].argTypes[k]` has bounded syntactic depth), the visited set strictly grows on every productive descent (each `.ref g` insert) and is bounded by `decls.size`. So within `decls.size + 1` recursion steps the visited saturates and any further `+1` bound is unused. Note: a pure rank witness alone is INSUFFICIENT — `.tuple`/`.array` nesting consumes bound at structural depth, and a deeply-nested type (e.g., `data T = ctor (.tuple [.tuple [.tuple [.field]]])`) requires bound `≥` syntactic depth + rank chain depth. The analytical sub-leaf must thread an additional structural-depth premise, OR rely on a source-language constraint that types in well-formed Aiur sources have bounded depth (currently not encoded in `WellFormed`). Mutual structural induction on `(rank dt, sizeOf t)` lex with the rank witness as the .ref-chain fuel and `sizeOf t` as the structural fuel. ~120 LoC.
2. **BLOCKED-dtFlatSize-mono-concrete**: Parallel to (1) on concrete side. Requires `rank_cd : Global → Nat` from `concretize_preserves_direct_dag` (orphan in Scratch.lean — see sorry #8). The chaining helper above is source-side only; a sibling `Concrete.dataTypeFlatSizeBound_mono_concrete_chain` would be needed for the concrete side at closure time, paralleling the planted source-side chain. ~150 LoC including the parallel chain helper.
3. **BLOCKED-dtFlatSize-bridge-perArgEq**: Discharge `_hPerArgEq` premise of #5d at the matched bound `M`. Composes `_hCtorArgsAlign` per-arg `MatchesConcreteFM` evidence with the typLevel sibling `typFlatSizeBound_eq_sizeBound_wf` at the bookkeeping `(visited, visited'.insert g)`. The typLevel's `_hVisDisj` premise is genuine under acyclicity: no constructor argType reaches a `.ref g'` for `g'` already in the dt-level visited (rank strict-decrease). ~80 LoC.
4. **BLOCKED-dtFlatSize-matched-bridge**: Apply `dataTypeFlatSizeBound_eq_sizeBound_wf` at matched bound `M` with discharged `_hPerArgEq` from (3) and bookkeeping bijection `visited.contains x ↔ visited'.contains x ∨ x = g` (which holds at empty visited sets after concrete's internal insert at `g`). ~30 LoC composition.

**Existing infrastructure to reuse**:
* `dataTypeFlatSizeBound_eq_sizeBound_wf` (#5d, closed) — matched-bound bridge.
* `typFlatSizeBound_eq_sizeBound_wf` (closed) — typLevel sibling for per-arg discharge.
* **`dataTypeFlatSizeBound_mono_source_chain`** (CLOSED 2026-05-04, planted at `Layout.lean` just before the saturation lemma) — `b₁ ≤ b₂ → (∀ b ∈ [b₁, b₂), step-mono at b) → mono at (b₁, b₂)` via induction on `b₂ - b₁`. Reduces sub-leaf 1 to its single-step companion `BLOCKED-dtFlatSize-mono-source-step`. Reachability keepalive added inside `dataTypeFlatSize_bound_saturation_wf`'s body so the orphan checker tracks the dependency.
* `Source.Decls.DeclsAgreeOnDtFM` (`MatchesConcrete.lean`, abbrev) — per-arg `MatchesConcreteFM` evidence.
* `Concrete.Typ.SpineRefsBelow` (`Ix/Aiur/Semantics/ConcreteInvariants.lean:238`) — rank-bound predicate for concrete side.
* `Typed.Decls.NoDirectDatatypeCycles` (`Ix/Aiur/Semantics/WellFormed.lean:132`) — typed-side rank witness.
* `wellFormed_implies_noDirectDatatypeCycles` (`Ix/Aiur/Proofs/CompilerProgress.lean:38`) — extracts the rank witness from `WellFormed t`. NOTE: lives downstream of Layout.lean; the saturation lemma's body must NOT call this directly (would create import cycle). Instead, the typed-side rank witness is passed implicitly through the `_hwf` premise; the body destructures `_hwf` via the `noDirectDtCycle` projection (TODO: verify the WellFormed structure exposes it locally; if not, the rank extraction may need to be hoisted as another premise).
* `concretize_preserves_direct_dag` — orphan in Scratch.lean (see sorry #8). Required for mono-concrete's rank transport.

**Dependencies on other sorries**:
* `BLOCKED-dtFlatSize-mono-concrete` depends on `concretize_preserves_direct_dag` (orphan, sorry #8 prerequisite).
* `BLOCKED-dtFlatSize-mono-source` is independent (only depends on the typed-side rank witness, which `WellFormed` provides directly).

**LoC estimate**: ~400 LoC total across the four sub-leaves (closure of all four collapses #5sat to sorry-free).

**Risk factors**:
* `BLOCKED-dtFlatSize-mono-concrete` has a hard dependency on `concretize_preserves_direct_dag`'s closure (orphan, ~500-700 LoC of its own). This may need to be hoisted as another premise of `dataTypeFlatSize_bound_saturation_wf` (taking `rank_cd` as a parameter) to break the dependency.
* The recursion in `BLOCKED-dtFlatSize-mono-source` requires careful management of the visited-set bookkeeping; the standard "rank-as-fuel" pattern needs adaptation because `dataTypeFlatSizeBound`'s `bound` parameter is a separate fuel from rank.
* `wellFormed_implies_noDirectDatatypeCycles` lives downstream of Layout.lean (CompilerProgress.lean). If the rank witness can't be extracted in Layout.lean's context, the saturation lemma may need to take the rank witness directly as a premise (`_hRank : ∃ rank, ...`) rather than via `WellFormed t`. Hoisting `_hRank` keeps Layout.lean independent of CompilerProgress.lean.

**Cascade unlock when closed**:
* #5e becomes sorry-free at the dt-level (already is, via #5sat dispatch).
* #11's bundled obligations in StructCompatible.lean (sorry #11*) drop the `_hDtFlatSizeAtTopBounds` discharge (was the dt-level part of the bundle).
* #13's eventual body in CompilerPreservation.lean drops the same discharge.
* The typLevel `BLOCKED-typFlatSize-bound-saturation` (parallel to dt-level) may need a sibling lemma `typFlatSize_bound_saturation_wf` — same proof skeleton but at the typLevel; can reuse the dt-level saturation as a sub-step.

---

### Sorry #8 — `sizeBoundOk_entry` (`CompilerProgress.lean:3639`)

**Sig**:
```
private theorem sizeBoundOk_entry
    {t : Source.Toplevel} {tds : Typed.Decls} {cd : Concrete.Decls}
    (_hwf : WellFormed t)
    (_hts : t.checkAndSimplify = .ok tds)
    (_hconc : tds.concretize = .ok cd)
    (_hacyclic : Typed.Decls.NoDirectDatatypeCycles tds)
    (_hunique : Typed.Decls.ConcretizeUniqueNames tds)
    (_hdtkey : Concrete.Decls.DtNameIsKey cd)
    (_htdDt : Typed.Decls.DtNameIsKey tds)
    (_htdCtorPresent : Typed.Decls.CtorPresent tds) :
    Concrete.Decls.SizeBoundOk cd
```

**Closure category**: Migrate orphan `concretize_produces_sizeBoundOk` (Scratch.lean:6957-7218) upstream + replace `FullyMono` consumer with entry-bridge.

**Closure path** (precise, step-by-step):
1. **Pre-requisite — close `DirectDagBody.spine_transfer`** (orphan, F=1, ~500-700 LoC, in Scratch.lean): backward-trace through `concretizeBuild` to show the spine of every dt in the post-fold concDecls is reachable from a source dt. This is the core blocker; the orphan stack at Scratch.lean:6957-7218 depends on it.
2. **Migrate `concretize_preserves_direct_dag` orphan** (Scratch.lean) to `ConcretizeSound/Layout.lean` or a new `DirectDag.lean` upstream module. Body composes `spine_transfer` with `concretizeBuild`'s structural lemmas.
3. **Migrate `sizeBound_ok_of_rank` orphan** (Scratch.lean, F=0, ~140 LoC) to `ConcretizeSound/Layout.lean`. Body: rank-based induction on dt graph (no concretize-specific content; pure graph-theoretic).
4. **Body of `sizeBoundOk_entry`** (after pre-reqs):
   - `obtain ⟨decls, hdecls⟩ := _hwf.mkDecls_ok`.
   - `have hRefClosed := Toplevel.concretize_produces_refClosed_entry _hwf hdecls _hts _hconc` (A.1).
   - `have hDirectDag := concretize_preserves_direct_dag _hacyclic _hunique _hconc` (Step 2).
   - `have hDtNameIsKey_cd := concretize_produces_dtNameIsKey _htdDt _hconc` (already F=0, used in caller at `CompilerProgress.lean:3751`).
   - Apply `sizeBound_ok_of_rank cd hRefClosed hDirectDag _hdtkey hDtNameIsKey_cd` (Step 3).
5. **Replace `hmono : FullyMonomorphic t`**: the orphan `concretize_produces_sizeBoundOk` consumes FullyMono via `concretize_produces_refClosed`. Replace with `Toplevel.concretize_produces_refClosed_entry` (Step 4 above).

**Existing infrastructure to reuse**:
- `Toplevel.concretize_produces_refClosed_entry` (A.1, in ConcretizeSound).
- `concretize_produces_dtNameIsKey` (F=0, in scope).
- The orphan stack in `Scratch.lean:6957-7218` (`concretize_produces_sizeBoundOk` + `concretize_preserves_direct_dag` + `sizeBound_ok_of_rank`) — migrate as part of closure.
- `DirectDagBody.spine_transfer` (Scratch.lean orphan) — main blocker, ~500-700 LoC of `concretizeBuild` backward-trace.
- `templateOf_of_source_ref` (referenced in PLAN as a sub-lemma) — search Scratch.lean.

**Dependencies on other sorries**: None at this layer; bottlenecked on closing `spine_transfer` (orphan, not in the 15 reachable sorries).

**LoC estimate**: ~30 LoC for the entry-bridge body; **plus** ~500-700 LoC for `spine_transfer` upstream + ~140 LoC for `sizeBound_ok_of_rank` migration + ~80 LoC for `concretize_preserves_direct_dag` migration. **Total**: ~750-950 LoC of upstream work.

**Risk factors**:
- `spine_transfer` is the largest single remaining piece; its closure path is sketched only at a high level in Scratch.lean. May benefit from a separate Plan agent.
- Migration order matters: `spine_transfer` → `concretize_preserves_direct_dag` → `sizeBound_ok_of_rank` → `sizeBoundOk_entry`. Skipping levels causes orphan-check regression.

---

### Sorry #9 — `function_compile_progress_entry` (`CompilerProgress.lean:3679`)

**Sig**:
```
private theorem function_compile_progress_entry
    {t : Source.Toplevel} {tds : Typed.Decls} {cd : Concrete.Decls}
    (_hwf : WellFormed t)
    (_hts : t.checkAndSimplify = .ok tds)
    (_hconc : tds.concretize = .ok cd)
    (_hunique : Typed.Decls.ConcretizeUniqueNames tds)
    (lm : LayoutMap) (_hlm : cd.layoutMap = .ok lm)
    (_hNameAgrees : ...) (_hDtNameIsKey : ...) (_hCtorIsKey : ...)
    (_hCtorPresent : ...) (_htdDt : ...) (_htdCtorPresent : ...)
    (_name : Global) (_f : Concrete.Function)
    (_hname : cd.getByKey _name = some (.function _f)) :
    ∃ body lms, Concrete.Function.compile lm _f = .ok (body, lms)
```

**Closure category**: Per-function compile progress (3-step composition); mirror of orphan `Function_compile_progress` (Scratch.lean:1153) with FullyMono-stripped.

**Closure path** (precise, step-by-step):
1. **Step 1 — Layout lookup succeeds**: `lm[_f.name]?` is `some (.function ...)`. Closure: `Concrete.Function.compile lm _f` first reads `lm[_f.name]?`. The layoutMap construction (`Concrete.Decls.layoutMap`'s fold) inserts a `.function` entry at every `.function` key (`layoutMapPass`'s `.function` arm). Since `cd.getByKey _name = some (.function _f)` and `_hNameAgrees` gives `_name = _f.name`, the lookup hits. Helper: ~80 LoC mechanical from `LayoutMap.layoutMap`'s structural construction; mirror of `concretize_layoutMap_progress`'s `.function` arm.
2. **Step 2 — Inputs foldlM succeeds**: `_f.inputs.foldlM (fun acc (l, t) => acc + typSize lm t) 0`. Closure: each `typSize lm _f.inputs[i].snd` succeeds via `Aiur.typSize_ok_of_refClosed_lm` (F=0, in `LowerShared.lean`). Composition is `inputs_foldlM_ok` (Scratch.lean:1382, F=0 modulo upstream); migrate to `LowerShared.lean` (mechanical).
3. **Step 3 — Body compile succeeds**: `_f.body.compile _f.output lm bindings |>.run state`. This is the deepest piece. Closure path:
   - `body_compile_ok` (Scratch.lean:1322, BLOCKED) — depends on `toIndex_progress_core_extended` IsCoreExtended-witness extraction + block-level dispatch + tail-form `Ctrl.compile_progress`.
   - `toIndex_progress_core_extended`: the IsCoreExtended witness packaged from `RefClosed cd` + `DtNameIsKey cd` + `CtorPresent cd` + `lm` agreement. Per-arm check that each Concrete-Term arm of `_f.body` produces a successful compile result. Companion to `toIndex_preservation_core_extended` from sorry #2.
   - `Ctrl.compile_progress`: tail-form compile success for `.match`/`.ret`/etc. ~100 LoC mechanical.
4. **Body composition** (after Steps 1-3 closed):
   - `unfold Concrete.Function.compile`.
   - Use Step 1 to discharge layout lookup.
   - Use Step 2 to discharge inputs fold.
   - Use Step 3 to discharge body compile.
   - Compose into `∃ body lms, ... = .ok (body, lms)`.
5. **Replace `hmono : FullyMonomorphic t`** in the orphan: `Function_compile_progress` consumes FullyMono via `concretize_produces_refClosed`; swap with `Toplevel.concretize_produces_refClosed_entry` (A.1).

**Existing infrastructure to reuse**:
- `Aiur.typSize_ok_of_refClosed_lm` (F=0, `LowerShared.lean`).
- `inputs_foldlM_ok` (Scratch.lean:1382, F=0 modulo migration).
- `body_compile_ok` (Scratch.lean:1322, F=1; BLOCKED on `toIndex_progress_core_extended`).
- `toIndex_progress_core_extended` (LowerShared.lean:165, F=1; sibling to `toIndex_preservation_core_extended`).
- `Toplevel.concretize_produces_refClosed_entry` (A.1).
- The orphan `Function_compile_progress` (Scratch.lean:1153) as the line-for-line template.

**Dependencies on other sorries**: Indirectly on sorry #2's blocker `toIndex_preservation_core_extended` (sibling shared with `toIndex_progress_core_extended`); closure of either's per-arm work amortizes.

**LoC estimate**: ~100 LoC for the headline composition body once dependencies migrated; **plus** ~400 LoC for `body_compile_ok` (Step 3) closure + ~80 LoC for Step 1's layout-map helper + ~50 LoC for `Ctrl.compile_progress`. **Total**: ~600-650 LoC.

**Risk factors**:
- `body_compile_ok` is the deepest piece; closure depends on the Concrete-Term shape being IsCoreExtended-classifiable, which currently is asserted but not extracted.
- Step 1's layoutMap-function-presence helper may surface a small upstream gap (the layoutMap's fold uniqueness for `.function` entries — parallel of sorry #4 but for `.function` arm).

---

### Sorry #11* — `compile_ok_implies_struct_compatible_of_entry` (`StructCompatible.lean:1554`)

**Status**: Bundled-hoist site for the 6 per-arm flat-size obligations from `typFlatSize_eq_typSize_under_match_wf` (whose body is itself sorry-free). Counts as ONE reachable sorry-using-decl.

**The 6 hoisted premises** (each shaped to match the `induction _hmatch` arm body):
1. `_hTupleArm` — per-position `MatchesConcreteFM` + per-position size IH ⟹ `.tuple` size equality.
2. `_hArrayArm` — inner `MatchesConcreteFM` + size IH ⟹ `.array` size equality.
3. `_hRefDispatch` — `typFlatSize decls {} (.ref g) = (typSize layoutMap (.ref g)).toOption.getD 0`. Discharged via `dataTypeFlatSize_eq_layoutMap_size_wf` + `layoutMap_dataType_size_extract` + bound-saturation.
4. `_hAppEmptyDispatch` — same shape as `_hRefDispatch`.
5. `_hAppResolvedDispatch` — bridges source `.app g args` to concrete `.ref concName` via mono-resolution invariant.
6. `_hAppUnresolvedDispatch` — bridges source `.app g args` to concrete `.ref g`.

**Closure path**: each arm's true closure requires bound-saturation (typLevel parallel of #5sat). Each arm composes:
- For ref-shaped arms (3/4/5/6): apply `dataTypeFlatSize_eq_layoutMap_size_wf` (#5e closed; takes `_hLKM`, `_hCdTdLenAgree`, `_hCtorArgsAlign`, `_hKeysAlign`) + `layoutMap_dataType_size_extract` (#4 closed; takes `_hLKM`).
- For structural arms (1/2): per-position IH composes via `Array.foldl`/`Array.mapM` length lemmas; saturation applied between IH bound and recursive bound.

**Premise discharge sources** (when consumer fills): `_hLKM` from `concretize_produces_dtNameIsKey` (CompilerProgress.lean:2816); `_hCdTdLenAgree` and `_hCtorArgsAlign` need new producers (mono-table semantics chain via StructCompatible's `concretize_extract_concF`); `_hKeysAlign` likewise; bound-saturation requires #5sat closure (or a typLevel parallel).

**Dependencies on other sorries**: #5sat (bound-saturation lemma) for the saturation argument. Indirectly on #5e/#5d (already closed).

**LoC estimate**: ~150-300 LoC for the 6-arm composition once #5sat closes.

**Risk factors**:
- The 6 arms share the bound-saturation blocker; closing them piecemeal does not reduce the count (bundled).
- Mono-table semantics chain (`concretize_extract_concF`) may need its own helper for the `appResolved` arm.

---

### Sorry #12 — `step_R_preservation_applyGlobal` (`Simulation.lean:355`)

**Sig**:
```
private theorem step_R_preservation_applyGlobal
    {decls : Source.Decls} {concDecls : Concrete.Decls}
    {funcIdx : Global → Option Nat}
    (_hDeclsR : Decls.R decls concDecls)
    (fuel : Nat) (name : Global) (args_src args_conc : List Value)
    (st_src : Source.Eval.EvalState) (st_conc : Concrete.Eval.EvalState)
    (_hStateR : StateR decls concDecls funcIdx st_src st_conc)
    (_hargsR : List.length args_src = List.length args_conc ∧
       ∀ i (h_src : i < args_src.length) (h_conc : i < args_conc.length),
         ValueR decls concDecls funcIdx args_src[i] args_conc[i]) :
    match Source.Eval.applyGlobal decls fuel name args_src st_src,
          Concrete.Eval.applyGlobal concDecls fuel name args_conc st_conc with
    | .ok (v_src, st_src'), .ok (v_conc, st_conc') =>
        ValueR decls concDecls funcIdx v_src v_conc ∧
          StateR decls concDecls funcIdx st_src' st_conc'
    | .error _, .error _ => True
    | _, _ => False
```

`Decls.R := CtorPreserved ∧ FnNamesAgree` (Simulation.lean ~line 350).
Both `CtorPreserved` (FWD-only, ValueEqFlatten.lean) and
`FnNamesAgree` (FWD-only, Simulation.lean) are bundled. Discharged
at `Toplevel.compile_preservation_entry` from caller-supplied
`_hDeclsR`, which `Toplevel.compile_correct` derives via the
entry-restricted kind-preservation chain (see Defect-1 cascade).

**Closure category**: Heart of cross-decls simulation; mutual recursion on fuel.

**Closure path** (precise, step-by-step):
1. **Sig form**: takes `_hDeclsR : Decls.R decls concDecls`. Cascade propagates through `concretize_runFunction_simulation` → `concretize_preserves_runFunction_entry` → `Toplevel.compile_preservation_entry` → `Toplevel.compile_correct`.
2. **Open `applyGlobal` on both sides**: `Source.Eval.applyGlobal decls fuel name args_src st_src` unfolds to `match fuel with | 0 => .error .outOfFuel | n+1 => match decls.getByKey name with | some (.function f) => ... | some (.constructor _ _) => ... | none => .error .unknownGlobal`. Same shape on concrete side.
3. **Fuel = 0 arm**: both sides return `.error .outOfFuel`; the goal's `.error _, .error _ => True` arm holds.
4. **Fuel = n+1, decls lookup splits**:
   - `.function f_src` source / `.function f_conc` concrete: lift `f_conc` via `_hFnNamesAgree`. Build the new bindings list using `_hargsR` pointwise (length match + per-position `ValueR`). Recurse via `step_R_preservation_term` (cross-mutual companion in Simulation.lean) at fuel `n` on `f_src.body` vs `f_conc.body`. The `.body` correspondence is supplied via a `TermBridge` predicate (`Simulation.lean:414+`); this requires sorry's body to invoke a `body_termBridge_at_function_key` helper — currently unmentioned, NEW ~80 LoC.
   - `.constructor dt_src c_src` source / `.constructor dt_conc c_conc` concrete (bridged by `_hCtorPreserved`): both sides build `.ctor name args`. Per-arg `ValueR` from `_hargsR`; for the new `.ctor` value, build `ValueR.ctor` with `h_ctor_flat_bridge` discharged via `flatten_agree_entry_ctor_bridge` (sorry #13).
   - `none` source / corresponding concrete `none` (under `_hFnNamesAgree`/`_hCtorPreserved` contrapositives): both sides error; `.error _, .error _ => True`.
5. **`step_R_preservation_term`** (cross-mutual): per-arm preservation of `R` through `Source.Term` evaluation. ~25 arms; each closes via the per-arm `TermBridge` constructor from `Simulation.lean:414+` plus per-arm bookkeeping. The `.app g args` arm recurses into `step_R_preservation_applyGlobal` at fuel `n-1` (the cross-decls call). Mutual recursion on `(fuel, term-size)` lex.
6. **Termination**: `termination_by fuel + sizeOf t` for the term-side companion, `fuel` for `applyGlobal`. Cross-call decrements fuel.
7. **Builds on the entry-side simulation framework already present in Simulation.lean**: `concretize_runFunction_simulation` (the public wrapper) consumes this lemma's output. Sig amendment must propagate to the wrapper's premises (caller package).

**Existing infrastructure to reuse**:
- `ValueR` predicate + `ValueR.{unit,field,pointer,tuple,array,ctor}` constructors (Simulation.lean:200+).
- `StateR` predicate + `entry_StateR_initial` (Simulation.lean:332).
- `TermBridge` inductive (Simulation.lean:414) — supplies the `f_src.body ↔ f_conc.body` correspondence.
- `Decls.CtorPreserved` (ValueEqFlatten.lean:241).
- `flatten_agree_entry_ctor_bridge` (sorry #13) — discharges the `.ctor` arm's `h_ctor_flat_bridge`.
- `ValueR_of_FnFree_at_entry` (Simulation.lean:294) — entry-shape `.ctor` arm template; `.tuple`/`.array` arms structurally identical here.

**Dependencies on other sorries**: Sorry #13's hoisted `_hCtorAgrees` (now bundled at #15) for the `.ctor` arm's `h_ctor_flat_bridge`. Sorry #1.C (`interp_MonoCtorReach`) provides the per-call `MonoCtorReach` propagation needed at the `.function` arm.

**LoC estimate**: ~400 LoC. Breakdown: ~30 LoC sig amendment + entry split, ~50 LoC fuel-zero + lookup-error arms, ~150 LoC `.function` arm (bindings build + cross-call recursion), ~100 LoC `.constructor` arm (`.ctor` value build + flat-bridge), ~80 LoC `step_R_preservation_term` cross-mutual companion (per-arm dispatch).

**Risk factors**:
- `TermBridge` correspondence at function bodies: requires `body_termBridge_at_function_key` helper that lifts `Concrete.Function.body = termToConcrete ∅ source_body`-like equation to a `TermBridge` witness. This may not exist; if absent, NEW ~80 LoC mirror of `step4Lower_function_origin` patterns.
- Cross-mutual termination on fuel: Lean may not infer; explicit `termination_by` annotation needed.

---

### Sorry #15 — `Toplevel.compile_correct` (`CompilerCorrect.lean:186`)

**Inner sub-sorry inventory** (post 2026-05-04 closure of `BLOCKED-CtorAgrees-index`): 2 granular leaves —
- `BLOCKED-CtorAgrees-flat-size` (within `hCtorAgreesAll.2`): `dataTypeFlatSize` agreement. Composition of `dataTypeFlatSize_eq_layoutMap_size_wf` (Layout.lean, F=2 with #5sat residual) with `Concrete.dataTypeFlatSize ↔ DataType.size` bridge. Requires LayoutKeysMatch + CdTdLenAgree + CtorArgsAlign + KeysAlign producer chains for the dt key (NOT the ctor key) at `dt_src.name`, lifted via `mkDecls_ctor_companion`. Acceptable residual under "if Layout-chain hoists aren't dischargeable, keep flat-size sub-blocker" clause.
- `BLOCKED-ConcreteApplyGlobalReach` (`hApplyGlobalReach`) — from #14's hoist; future closure plants `Concrete.MonoCtorReachBody` mirror of source-side `MonoCtorReachBody`.

**`BLOCKED-CtorAgrees-index` CLOSED 2026-05-04**: planted `PhaseA2.concretizeBuild_at_typed_ctor_at_entry_fwd` in `ConcretizeSound/CtorKind.lean` (single-key entry-restricted variant of `_explicit_general` — uses `ConcretizeUniqueNames` to derive `hDtNotKey`/`hFnNotKey` and the `hPerDtWit` builder's `args = #[]` step instead of universal `params_empty`). Closure body in `compile_correct.hCtorAgreesAll.1`: derives `dt_src.params = []` via `concretizeBuild_ctor_origin` 2-way classification (origin 1 directly through FnMatchP, origin 4 via `ConcretizeUniqueNames` on the `concretizeName g_orig args = concretizeName dt_src.name #[]` collision anchored by `concretizeBuild_containsKey_newDt_name` + step4Lower keys-iff), then applies the new variant + `step4Lower_constructor_explicit` + nameHead-based distinctness transfer to derive `findIdx?`-positional agreement.

**`hCtorPreserved` and `hDeclsR` clauses are CLOSED** end-to-end (no sub-sorries): the architectural-defect closure (2026-05-04) made `Decls.CtorPreserved` and `Decls.FnNamesAgree` FWD-ONLY (dropping the structurally-False BWD halves). The 3 BWD-phantom sub-sorries (`BLOCKED-CtorPreserved-BWD` ×2 and `BLOCKED-FnNamesAgree-BWD`) are gone. See "Sig amendments 2026-05-04 — Defect 2 (architectural follow-up)" at the bottom for the rationale.


**Sig**:
```
theorem Toplevel.compile_correct
    (t : Source.Toplevel) (hwf : WellFormed t) :
    (∃ ct decls, t.mkDecls = .ok decls ∧ t.compile = .ok ct)
    ∧
    (∀ ct decls, t.mkDecls = .ok decls → t.compile = .ok ct →
      ∀ name funIdx _hname f _hsrc _hentry args io₀ fuel retTyp _hargsFnFree _hargsReach,
        InterpResultEq decls ct.globalFuncIdx retTyp
          (Source.Eval.runFunction decls (Global.mk name) args io₀ fuel)
          (Bytecode.Eval.runFunction ct.bytecode funIdx
            (Flatten.args decls ct.globalFuncIdx args) io₀ fuel))
```

**Closure category**: Top-level composition; the body composes `compile_progress_entry` + `compile_preservation_entry`, with 3 granular sub-sorries documented above.

**Closure status (post 2026-05-04 architectural-defect closure)**:
1. **`hCtorPreserved`** — CLOSED end-to-end via the 3-step chain `checkAndSimplify_preserves_ctor_kind_fwd` (CheckSound) + `concretizeBuild_preserves_ctor_kind_at_entry_fwd` (Phase4) + `step4Lower_preserves_ctor_kind_fwd` (CtorKind). The previously paired BWD-phantom sub-sorry was dropped together with the structurally-False BWD half of `Decls.CtorPreserved`.
2. **`hDeclsR`** — CLOSED end-to-end for both `Decls.CtorPreserved` and `Decls.FnNamesAgree` clauses (FWD-only sigs). Function variant chain: `concretizeBuild_preserves_function_inputs_at_entry_fwd` (Phase4) + `step4Lower_function_explicit` (Shapes) + inline `mapM_first_proj` helper for the `inputs.map (·.1) = inputs.map (·.1)` propagation. The two BWD-phantom sub-sorries were dropped.
3. **`hCtorAgreesAll`** — index-half CLOSED 2026-05-04 (uses new `PhaseA2.concretizeBuild_at_typed_ctor_at_entry_fwd` in CtorKind.lean — single-key entry-restricted variant of `_explicit_general` that uses `ConcretizeUniqueNames` in lieu of universal `params_empty`); flat-size half (`BLOCKED-CtorAgrees-flat-size`) remains as the only outstanding `hCtorAgreesAll` sub-sorry.
4. **`hApplyGlobalReach`** — untouched; awaits `Concrete.MonoCtorReachBody` namespace plant.

**Composition body** (lines 191-282): 
- (a) Progress: `Toplevel.compile_progress_entry t hwf` (CompilerProgress.lean — entry-restricted progress, body composes through sorries #8, #9).
- (b) Preservation: at the call site, derives `hcdNameAgrees` (F=0), `hconcRetFnFree` via `Toplevel.compile_correct_concRetFnFree_entry` (F=0, lines 92-139), `hconcRetReach` via `Concrete.Eval.runFunction_preserves_MonoCtorReach` wired with `hCtorPreserved` (FWD-closed) + `hApplyGlobalReach` (still BLOCKED).
- Final dispatch to `Toplevel.compile_preservation_entry`.

**Existing infrastructure to reuse**:
- `Toplevel.compile_progress_entry` (CompilerProgress.lean) — wraps sorries #8, #9.
- `Toplevel.compile_preservation_entry` (CompilerPreservation.lean) — wraps sorries #2, #10, #11, #13.
- `Toplevel.compile_correct_concRetFnFree_entry` (CompilerCorrect.lean:92, F=0).
- `Concrete.Eval.runFunction_preserves_MonoCtorReach` (sorry #14).
- `concretizeBuild_preserves_ctor_kind_at_entry_fwd` (Phase4.lean) — ctor mirror of function-kind variant.
- `step4Lower_fold_ctor_bridge_inline` (Shapes.lean) — mono → concrete ctor lift.
- `checkAndSimplify_preserves_ctor_kind` (CheckSound.lean — verify).

**Dependencies on other sorries**: ALL OTHER REACHABLE SORRIES — `compile_correct` is the headline composition. The 4 inner BLOCKED leaves are discharge-points for cascaded hoists from #13 (`hCtorAgreesAll`), #14 (`hApplyGlobalReach`), Defect 1 (`hDeclsR`), and the original A.5 ctor-bridge (`hCtorPreserved`). Wider composition depends on #1.C, #2, #5sat, #8, #9, #11*, #12.

**LoC estimate**: ~30-50 LoC for the inner `hCtorPreserved` derivation (Steps 1-3). Outer body already wired.

**Risk factors**:
- **`concretizeBuild_preserves_ctor_kind_at_entry_fwd` status uncertainty**: PLAN PER-ITEM 13 references this as needing ~400 LoC. If it's not closed, that's an UPSTREAM ~400 LoC dependency hidden under the inner sorry.
- The `Decls.CtorPreserved` predicate is universal over all `g`; entry-restricted lifts may not cover non-entry-reachable `g`. Verify `WellFormed.notPolyEntry` propagation through the dt graph reaches every ctor — or restrict `CtorPreserved` to entry-reachable ctors (sig amendment to `runFunction_preserves_MonoCtorReach`).
- The `_hargsReach` caller-witness obligation (the second sub-sorry of the original `compile_correct` body, mentioned in the PLAN summary as having been hoisted to a caller premise): now provided as a hypothesis via `_hargsReach` parameter, so the inner-sorry count is reduced to ONE (the `hCtorPreserved` derivation at line 276).

---

## ConcretizeSound module split (locked)

`ConcretizeSound.lean` 89 LoC facade + 12 sub-modules under `Ix/Aiur/Proofs/ConcretizeSound/`:
- `MonoInvariants.lean` — Phase 2 + MonoHasDecl + MonoShapeOk
- `FnFree.lean` — FnFreeBody mutual + `runFunction_preserves_FnFree`
- `FirstOrder.lean` — FO drain chain + PendingArgsFO + mkParamSubst-total lemmas
- `RefsDt.lean` — TermRefsDt full chain
- `StageExtract.lean` — typFlatSize + Phase A.1
- `Layout.lean` — concretize_layoutMap_progress
- `Shapes.lean` — StrongNewNameShape + IndexMap + step4Lower key helpers (ctor/dt/fn explicit lemmas)
- `CtorKind.lean` — Phase A.2/A.3 + reverse origin + Phase 0 + DirectDagBody (origin lemmas + concretizeBuild_at_*_explicit family + CtorArgsRewrittenFrom/DtRewrittenFrom/FnRewrittenFrom/DtCompanionRewrittenFrom predicates)
- `Phase4.lean` — Phase A.4 + Phase B prereq
- `RefClosed.lean` — A.1 umbrella + AppRefToDt/AppRefToDtOrNewDt predicates + drain-AppRefToDt invariant chain (CtorArgs/PendingArgs/NewFn{Inputs,Output}AppRefToDt)
- `SizeBound.lean` — sizeBoundOk + SpineRefsBelow + Wire B = C.1
- `TypesNotFunction.lean` — TypesNotFunction full chain

DrainInvariants.lean (Semantics): `DrainState.{NewDtFullShape, NewFnFullShape}` (canonical-shape dedup invariants).

All `private` declassified. Stage IRs (`Stages/{Concrete,Simple,Typed}.lean`) marked `@[expose] public section`.

## Three invariants

### Invariant 1 — Wiring discipline

Every theorem in `Ix/Aiur/Proofs/*.lean` (except `compile_correct` and `Scratch.lean`) MUST be transitively reachable from `Aiur.Toplevel.compile_correct`.

- **Verify**: `lake env lean tools/OrphanCheck.lean`.
- **Tooling caveat**: false positives on mutual-block peers. Handled in `tools/CheckReach.lean` via `info.all`.

### Invariant 2 — No body sorries

Every `sorry` is the entire body of a named theorem with sig + docstring, OR a named internal sub-claim (with `BLOCKED-<tag>` note) inside a structurally-decomposed proof.

### Invariant 3 — No sig-fixes outside PLAN amendments

PLAN locks current signatures. Sig changes require explicit amendment.

## Architecture

```
Source.Toplevel
  ├── mkDecls          → Source.Decls
  ├── checkAndSimplify → Typed.Decls
  ├── concretize       → Concrete.Decls
  ├── lower            → bytecode + preNameMap
  └── deduplicate      → bytecode + remap
```

`compile_correct` body REAL composition through:
1. `compile_progress_entry` (Progress)
2. `compile_preservation_entry` (Preservation)
3. `compile_correct_concRetFnFree_entry` (FnFree projection)

## Strategic insight

`Source.Function.notPolyEntry`: every entry has `params = []` (Aiur structural invariant; no polymorphic public entries).

`concretize`'s drain monomorphizes the transitive call graph from entries. Per-entry monomorphism propagates structurally. Proofs about `cd` rely on `cd`'s drain-mono shape (`StrongNewNameShape`, `FullShape` etc.) — never constrain source globally.

`WellFormed` accepts polymorphic Aiur (e.g. IxVM `List<T>`, `Option<T>`); FullyMonomorphic was removed 2026-04-26.

## Tooling

### `tools/OrphanCheck.lean`
**Run**: `lake env lean tools/OrphanCheck.lean`
Walks `compile_correct`'s transitive constant closure. Reports user-authored theorems in `Ix/Aiur/Proofs/*.lean` not in closure.

### `tools/CheckReach.lean`
**Run**: `lake env lean tools/CheckReach.lean`
Verifies a candidate list of theorems is reachable from `compile_correct`.

### `tools/migrate_orphans.py`
**Run**: `python3 tools/migrate_orphans.py [--file F.lean]`
Mechanical orphan migrator. Cuts orphan theorems → Scratch.lean.

### `tools/theorem-stats.py`
**Run**: `python3 tools/theorem-stats.py`. Output: `tools/theorem-stats.md`.
Numerical analysis: per-file theorem counts, sorry hot-spots, distance from `compile_correct`.

## Self-management guidelines

### Before coding

1. **Plan first.** For any closure >50 LoC, dispatch Plan agent OR write upfront enumeration: lemmas needed, sigs, dependencies, expected sorry-count delta.
2. **Read templates.** Find existing similar proof. Copy structure, swap conclusion.
3. **Verify API existence.** Before using a lemma, grep existing usage to confirm sig.
4. **Mock-first assembly.** For multi-lemma chains: write OUTER theorem body FIRST using `have h_i : sig_i := sorry` for each planned helper. Verify sigs ASSEMBLE before writing 100s of LoC.

### During coding

5. **One lemma per checkpoint.** Build green after each new lemma.
6. **Watch `Array.foldl` vs `List.foldl`.** Confirm field type.
7. **`HashSet.mem_insert` direction**: `(insert_key == query) = true ∨ query ∈ s`.
8. **Avoid `simp [h]` on conditionals.** Use `rw [if_pos h]` / `rw [if_neg h]` explicitly.
9. **`subst` on `let`-bindings fails.** Use `have := …`.
10. **`unfold` requires `@[expose]`.** Mark upstream.

### Recovery

11. **Regression policy.** Sorry-count increase from a *decomposition* (one monolithic sorry → N granular sub-leaves with `BLOCKED-` tags) is acceptable when each new leaf is reachable and has a precise sig + closure path. In that case, every new sorry MUST be added to PLAN.md with a rigorous proving plan (sig, closure path, infra to reuse, deps, LoC estimate, risk factors) before the iter ends. Hard-revert ONLY when the increase is from broken work (sigs that don't compose, leaves that aren't reachable, no plan).
12. **Keep new helpers small.** Each new theorem ≤ 80 LoC. Bigger = decompose first.
13. **Orphan helpers acceptable temporarily.** Will become reachable when chain completes.

### Stopping criteria

14. **Time budget per attempt: ~30 min** (extend to ~60 min for well-scoped agent dispatches).
15. **Track delta per iter.** End each iter with `lake build 2>&1 | grep "uses sorry" | wc -l`. Must be ≤ baseline.
16. **Amend topmost commit** after each green checkpoint (per branch directive).

### PLAN.md cleanliness

PLAN.md is forward-looking only. When a sorry closes:
- Strip its `### Sorry #N` rigorous-plan section entirely (do not mark it CLOSED).
- Strip its row from the inventory table.
- Remove inline `(CLOSED ...)` / `✅` markers; clean up any follow-up notes that only made sense relative to the closure.
- Remove any `~~strikethrough~~` text introduced when the closure superseded an old note; keep only the current statement.
Closure history → commit messages, not PLAN.md.

### Pivot signals

17. **Multi-helper threading taking >2 iters → switch to from-scratch single-theorem proof.** Avoid touching reachable theorems for sig changes.
18. **Disjointness premises blocking → check if hUnique + cd-side invariant + kind-conflict closes** (collision-witness pattern).
19. **External sorry stalled → write helpers AHEAD as orphans, wire later.**

### Subagent dispatch

For multi-hundred-LoC mechanical work (mirror chains, drain invariants, structural extensions), dispatch sub-agent with:
- Clear sig of target theorems.
- Pointers to existing infrastructure to reuse.
- Template references (closed parallel proofs).
- Constraint: don't break build; plant detailed BLOCKED notes if stuck.

## Methodology

### Per-leaf workflow

1. Read theorem at given location. Verify sig matches PLAN.
2. Build closure using ONLY:
   - Predicates/lemmas already in scope.
   - Closure path documented above.
3. Test via `lake build`. Use `#exit` for fast iteration in big files.
4. Amend topmost commit on success.
5. Sig changes require PLAN amendment.

### Closure validation

- [ ] `lake build` green.
- [ ] Sorry count strictly decreases OR internal leaves precisely named.
- [ ] OrphanCheck reports unchanged or fewer orphans.
- [ ] Any new helper cited from `compile_correct`'s closure (via CheckReach).

### Banned

- `sed`, `awk`, `head`, `tail`, `cat` for file I/O — use `Read`.
- `lake test` during agent runs.
- `> /tmp/file` redirects (trigger approval prompts).
- Sig changes outside PLAN amendments.

## Done definition

`compile_correct` is closed when:

1. `lake build` green.
2. **ZERO sorries reachable from `compile_correct`** — every sorry in the transitive closure (per `tools/CheckReach.lean`) is closed.
3. **ZERO orphan theorems in `Ix/Aiur/Proofs/*.lean`** (excluding `Scratch.lean`).
4. `lake test -- aiur-cross` green.
5. `WellFormed` accepts polymorphic Aiur (IxVM `core` should satisfy via `notPolyEntry` discharge).

When (1)+(2)+(3) hold → deliver this PR.

---

## Sig amendments 2026-05-04 — defect closures

Three audit-identified defects: every formerly hoisted-as-False premise now
takes a properly-bound side condition that admits an actual witness in the
caller's context. Sorry count unchanged (9 → 9); each remaining sorry's sig
is provable.

### Defect 1 — `#11 layoutMap-binding`

**What was wrong**: 6 hoisted premises in `Ix/Aiur/Proofs/StructCompatible.lean`
universally quantified over `layoutMap : LayoutMap` without constraining it
to the actual `concDecls.layoutMap` output. Counterexample: `layoutMap = ∅`
makes `typSize ∅ (.ref g) = .error`, so `(typSize ∅ (.ref g)).toOption.getD
0 = 0`. But for non-empty source dt, `typFlatSize decls {} (.ref g) = 1`.
Therefore `1 ≠ 0` ⟹ False under the universal-over-`layoutMap` shape.

**What was changed**: each premise now takes `{layoutMap : LayoutMap}
(_hLM : concDecls.layoutMap = .ok layoutMap)` upfront, binding `layoutMap`
to the actual decoded map. At `compile_ok_input_layout_matches_entry` the
premises additionally carry `concDecls`/`typedDecls` existentials with
`hts`/`hconc` so the consumer at `compile_ok_implies_struct_compatible_of_entry`
can supply them via `compile_stages_of_ok hct`.

**Cascade points** (all in `Ix/Aiur/Proofs/StructCompatible.lean`):
- `concretize_extract_concF_flat_size_bridge_wf` (~line 1213) — premises
  re-shaped; body unchanged save for `_hX hlayout` argument insertion.
- `concretize_extract_concF_at_reachable_wf` (~line 1316) — premises
  re-shaped; body unchanged (forwards verbatim).
- `compile_ok_input_layout_matches_entry` (~line 1434) — premises
  re-shaped to take `concDecls`/`typedDecls`/`hts`/`hconc`/`_hLM`; body
  threads `hts hconc` from `compile_stages_of_ok` into each premise.
- `compile_ok_implies_struct_compatible_of_entry` (~line 1599) — the 6
  inline `sorry` stubs re-arity'd from `fun _ ... => sorry` to match the
  new premise signatures (each adds 2-3 extra parameters).

**Files touched**: 1 (`StructCompatible.lean`).
**Call sites updated**: 3 (the three `concretize_extract_concF_*` /
`compile_ok_input_layout_matches_entry` consumer chains).

### Defect 2 — `#15/#12 CtorPreserved + FnNamesAgree universal-over-decls`

**What was wrong**: `Decls.CtorPreserved` (`ValueEqFlatten.lean:249`) and
`Decls.FnNamesAgree` (`Simulation.lean:363`) universally quantified the FWD
direction over all source decl entries. Polymorphic source like `data
Option<T> { None, Some(T) }` has `decls.getByKey "Option.None" = .constructor
poly_dt c` with `poly_dt.params = ["T"]`, but `concDecls` only contains
monomorphic variants at `concretizeName "Option.None" #[U64] = "Option_U64.None"`
— NOT at bare `"Option.None"`. So `concDecls.getByKey "Option.None" = none`
universally falsifies the FWD direction. Same counterexample for polymorphic
functions and `FnNamesAgree`.

**What was changed (initial pass)**:
- `Decls.CtorPreserved` FWD took `dt.params = []` as an additional
  hypothesis. BWD initially exposed `dt.params = []` in the conclusion's
  conjunct (later dropped — see architectural follow-up below).
- `Decls.FnNamesAgree` FWD took `f_src.params = []`. BWD initially
  exposed `f_src.params = []` (later dropped).
- `Value.MonoCtorReach.ctor`'s `hsrc` field strengthened to carry
  `dt.params = []` (the predicate is structurally tightened so only
  ctors with monomorphic dt can witness it).
- `Value.MonoCtorReach.ctor_src` projection updated to expose
  `dt.params = []`.
- `MonoCtorReachBody.{applyGlobal, applyLocal, interp, evalList,
  evalMatchCases}_MonoCtorReach` and `runFunction_preserves_MonoCtorReach`
  now take a `_hDeclsParamsEmpty : ∀ g dt c, decls.getByKey g = some
  (.constructor dt c) → dt.params = []` premise. This is the universal
  variant required at the `applyGlobal_MonoCtorReach.constructor` build
  site (the runtime guard alone doesn't yield `dt.params = []`).
  **Truth-value note**: this universal premise is provably False under
  polymorphic source (e.g. `Option<T>`'s "Option.None" has `dt.params =
  ["T"] ≠ []`). However, the source-side `runFunction_preserves_MonoCtorReach`
  is currently only referenced as a type-level keepalive in
  `Concrete.Eval.runFunction_preserves_MonoCtorReach` (no real caller
  dispatches through it from `compile_correct`), so the premise's
  truth-value is not load-bearing in any reachable proof. A future
  tightening should replace this with a per-call entry-reachability
  guard (e.g. `_hReachable g → dt.params = []`) once the source-side
  evaluator's reachable role from `compile_correct` is determined.

**Cascade points**:
- `Ix/Aiur/Proofs/ValueEqFlatten.lean`:
  - `Decls.CtorPreserved` definition (line ~257).
  - `Value.MonoCtorReach.ctor` constructor + `ctor_src` projection (lines
    143, 164).
  - `applyGlobal_MonoCtorReach.constructor` arm — uses `_hDeclsParamsEmpty`
    to derive `dt.params = []` for both the strengthened `hsrc` field and
    `_hCtorPreserved`'s params-empty argument.
  - `applyLocal_MonoCtorReach`, `evalList_MonoCtorReach`,
    `evalMatchCases_MonoCtorReach`, `interp_MonoCtorReach` — premise
    threaded.
  - `runFunction_preserves_MonoCtorReach` — premise threaded; dispatches
    to `applyGlobal_MonoCtorReach` and `interp_MonoCtorReach` with it.
- `Ix/Aiur/Proofs/Simulation.lean`:
  - `Decls.FnNamesAgree` definition.
- `Ix/Aiur/Proofs/CompilerPreservation.lean`:
  - `flatten_agree_entry.ctor` arm — `hreach.ctor_src` now yields
    strengthened `∃ dt c, ... ∧ dt.params = []`; weakened locally to the
    bridge's existing `∃ dt c, ...` shape via destructuring + re-pack.
    Bridge sig unchanged (the bridge body doesn't yet consume
    `dt.params = []`; future cascade can tighten if needed).

**Files touched**: 3 (`ValueEqFlatten.lean`, `Simulation.lean`,
`CompilerPreservation.lean`).
**Call sites updated**: 6 (all `MonoCtorReachBody.*` calls to peers
internally; `runFunction_preserves_MonoCtorReach`'s dispatch; the
`flatten_agree_entry.ctor` weakening adapter).

### Defect 2 (architectural follow-up) — `Decls.CtorPreserved` and `Decls.FnNamesAgree` BWD halves dropped

**What was still wrong after the initial pass**: the predicates were
made BICONDITIONAL (FWD ∧ BWD). The BWD direction said: "every concrete
`.constructor` (resp. `.function`) key has a source preimage at the
SAME key, with `dt.params = []` (resp. `f_src.params = []`)". This is
provably False on polymorphic source: drained `newDataTypes` /
`newFunctions` produces concrete entries at MANGLED keys
(`concretizeName g_orig args .pushNamespace c.nameHead` etc.) with no
source entry at the mangled key. Keeping BWD as a biconditional with
phantom `BLOCKED-CtorPreserved-BWD` and `BLOCKED-FnNamesAgree-BWD`
sub-sorries hid an unprovable obligation behind a fraudulent hoist.

**Why the initial pass made them biconditional**: the rationale was
that the concrete-side `Concrete.Eval.runFunction_preserves_MonoCtorReach`
mirror, when planted, would need the BWD direction to extract a
source-side witness for `Value.MonoCtorReach.ctor`'s `hsrc` field on
the runtime guard `concDecls.getByKey g = some (.constructor _ _)`. But
on closer inspection:

1. The concrete-side `runFunction_preserves_MonoCtorReach` body
   (`CompilerCorrect.lean:72-104`) currently HOISTS the obligation to
   the `_hApplyGlobalReach` premise — it doesn't itself project on
   `_hCtorPreserved.2`.
2. The source-side `MonoCtorReachBody.applyGlobal_MonoCtorReach` only
   uses the FWD direction (`_hCtorPreserved.1` projection in the
   `.constructor` arm).
3. Future `Concrete.MonoCtorReachBody` (when planted) WILL need a
   source-side witness for `MonoCtorReach.ctor`'s `hsrc` field, but
   the right shape is **template-name** resolution (concrete key →
   look up template `(g_orig, args)` via the drain map → source
   `g_orig` is a non-mangled source key with `dt.params = []`), NOT
   same-key BWD. That is a DIFFERENT predicate to be introduced when
   needed (`Decls.CtorTemplate` or similar).

**What was changed**:
- `Decls.CtorPreserved` is now FWD-ONLY (`ValueEqFlatten.lean`).
- `Decls.FnNamesAgree` is now FWD-ONLY (`Simulation.lean`).
- All `_hCtorPreserved.1` projections changed to direct application
  (`_hCtorPreserved g dt c hfg hParamsEmpty`).
- 3 BWD-phantom sub-sorries removed from `Toplevel.compile_correct`'s
  body: `BLOCKED-CtorPreserved-BWD` (in `hCtorPreserved`),
  `BLOCKED-CtorPreserved-BWD` (in `hDeclsR.1`),
  `BLOCKED-FnNamesAgree-BWD` (in `hDeclsR.2`).

**Cascade points**:
- `Ix/Aiur/Proofs/ValueEqFlatten.lean`:
  - `Decls.CtorPreserved` definition reduced to FWD-only.
  - `applyGlobal_MonoCtorReach`: `_hCtorPreserved.1` → `_hCtorPreserved`.
- `Ix/Aiur/Proofs/Simulation.lean`:
  - `Decls.FnNamesAgree` definition reduced to FWD-only.
- `Ix/Aiur/Proofs/CompilerCorrect.lean`:
  - `compile_correct.hCtorPreserved`: `refine ⟨FWD, BWD-sorry⟩` → direct
    FWD-only proof.
  - `compile_correct.hDeclsR`: `refine ⟨⟨FWD, BWD-sorry⟩, ⟨FWD, BWD-sorry⟩⟩`
    → `refine ⟨FWD, FWD⟩` direct.

**Files touched**: 3 (`ValueEqFlatten.lean`, `Simulation.lean`,
`CompilerCorrect.lean`).
**Sub-sorries removed**: 3 (`BLOCKED-CtorPreserved-BWD` ×2 and
`BLOCKED-FnNamesAgree-BWD`).
**Build status**: green; CheckReach (reachability) clean.

### Defect 3 — `#5sat / #8 spine_transfer hoist`

**What was wrong**: `DirectDagBody.spine_transfer` (Scratch.lean:6894)
needed an invariant "under `hunique` + `concretizeName_empty_args g' = g'`,
any template `(templateName', args')` with `concretizeName templateName'
args' = g'` must satisfy `templateName' = g' ∧ args' = #[]" — which the
docstring named but the sig didn't carry. Without it the `.ref g'` arm of
the structural induction can't reduce `rank_cd g' < rank_cd g` to the
source-side inequality.

**What was changed**: added `_hDrainShape : ∀ g' templateName' args', (∃
cdt' : Concrete.DataType, cd.getByKey g' = some (.dataType cdt')) →
concretizeName templateName' args' = g' → templateName' = g' ∧ args' = #[]`
as a premise on `spine_transfer`.

**Cascade points** (all in `Scratch.lean`, orphan cluster):
- `DirectDagBody.spine_transfer` (~line 6894) — sig amended.
- `concretize_preserves_direct_dag` (~line 6935) — discharges
  `_hDrainShape` via a new BLOCKED-spine-transfer-drain-shape sub-sorry.
  Discharge plan: compose `ConcretizeUniqueNames` (uniqueness of
  `(templateName, args)` producing each cd-key) with `StrongNewNameShape`
  (cd-keyed dataTypes are either source-monomorphic with
  `concretizeName g #[] = g`, or drain-produced with the canonical
  `(templateName, args)` recorded in `mono`). When migrated upstream
  for #8 closure, both should land in `ConcretizeSound/SizeBound.lean`
  next to the rest of the rank-witness chain.

**Files touched**: 1 (`Scratch.lean`).
**Call sites updated**: 1 (consumer in same file). Note: orphan cluster,
not currently in `compile_correct`'s reachable closure; the amendment
takes effect when migrated upstream for #8 (`sizeBoundOk_entry`).

### New BLOCKED sub-sorries planted

- `BLOCKED-spine-transfer-drain-shape` in `Scratch.lean`'s
  `concretize_preserves_direct_dag` (orphan, doesn't change reachable
  count).

No new BLOCKED tags planted in reachable theorems. The Defect 2 cascade
required threading a new `_hDeclsParamsEmpty` premise through the
`MonoCtorReachBody` mutual block — discharged at the consumer
`runFunction_preserves_MonoCtorReach` (also a hypothesis there) and
ultimately at `compile_correct` via the still-existing `BLOCKED-
CtorPreserved-from-entry-compilation` sorry, which now owns the
discharge of `_hDeclsParamsEmpty` as part of the entry-reachability chain.

### Sub-leaf decomposition 2026-05-04 — `dataTypeFlatSizeBound_mono_source_chain`

**What was added**: a new closed helper theorem
`dataTypeFlatSizeBound_mono_source_chain` planted in
`Ix/Aiur/Proofs/ConcretizeSound/Layout.lean` immediately before
`dataTypeFlatSize_bound_saturation_wf` (#5sat). The helper takes a
"single-step monotonicity" hypothesis (`∀ b ∈ [b₁, b₂),
dataTypeFlatSizeBound decls b visited dt = dataTypeFlatSizeBound
decls (b+1) visited dt`) plus `b₁ ≤ b₂`, and chains them by induction
on the gap `b₂ - b₁` to derive any-bound monotonicity
(`dataTypeFlatSizeBound decls b₁ visited dt = dataTypeFlatSizeBound
decls b₂ visited dt`).

**Sig**:
```
theorem dataTypeFlatSizeBound_mono_source_chain
    (decls : Source.Decls)
    {visited : Std.HashSet Global} {dt : DataType}
    {b₁ b₂ : Nat} (hb : b₁ ≤ b₂)
    (hStep : ∀ b, b₁ ≤ b → b < b₂ →
       dataTypeFlatSizeBound decls b visited dt =
         dataTypeFlatSizeBound decls (b+1) visited dt) :
    dataTypeFlatSizeBound decls b₁ visited dt =
      dataTypeFlatSizeBound decls b₂ visited dt
```

**Body**: closed (no sorry). ~30 LoC of standard `Nat` induction on the
gap `b₂ - b₁`.

**Why**: the original `BLOCKED-dtFlatSize-mono-source` sub-leaf
(sub-leaf 1 of #5sat) bundled both the chaining arithmetic and the
analytical step content. Factoring out the chain proof lets the
content-free arithmetic close unconditionally while the genuine
analytical claim — the single-step `dataTypeFlatSizeBound decls b
visited dt = dataTypeFlatSizeBound decls (b+1) visited dt` for
`b ≥ saturation level` — sits behind a precise BLOCKED tag
(`BLOCKED-dtFlatSize-mono-source-step`) for resumption.

**Wiring**: `dataTypeFlatSize_bound_saturation_wf`'s body adds a
reachability keepalive (`let _hChainSrc := @dataTypeFlatSizeBound_mono_source_chain`)
so the orphan checker tracks the new helper as transitively reached
from `compile_correct`.

**Net delta**: 1 of 4 BLOCKED sub-leaves of #5sat partially closed
(chain arithmetic discharged; analytical content still pending).
Headline reachable sorry count unchanged (9 → 9) since #5sat itself
is still a single bundled sorry.

**Files touched**: 2 (`Ix/Aiur/Proofs/ConcretizeSound/Layout.lean`,
`PLAN.md`).
**Build status**: green; CheckReach clean; the new helper is
REACHED (verified via `lake env lean tools/OrphanCheck.lean`).

**Analytical sub-leaf still BLOCKED — `BLOCKED-dtFlatSize-mono-source-step`**:
the genuine claim is that for `b ≥ decls.size + 1` (or whatever the
saturation level turns out to be), adding 1 to the bound doesn't
change the value. **A pure rank witness alone is INSUFFICIENT**: a
`.tuple`/`.array` nesting at depth `D` consumes `D` units of bound at
syntactic descent, independent of the rank witness which only bounds
.ref-chain depth. So a deeply-nested type (e.g.
`data T = ctor (.tuple [.tuple [.tuple [.field]]])`) requires bound
`≥ D + rank-chain-depth + 1`. Closing the analytical sub-leaf
requires either:
- a structural-depth bound on every `t` in
  `decls.dataTypes[i].constructors[j].argTypes[k]` (currently not
  encoded in `WellFormed`), OR
- restricting the source language so `.tuple`/`.array` nesting is
  bounded by `decls.size` (a simple syntactic check on
  `t.dataTypes`), OR
- amending the saturation lemma's sig to take the matched bound `M`
  as a parameter (delegating mono-source/concrete to the consumer
  who has access to `WellFormed`'s typed-side rank witness
  transported through `mkDecls`/`checkAndSimplify` and additional
  source-text-bound invariants).

---

## Sig amendments 2026-05-04 (second-pass defects) — `typFlatSize` widening + `RefsDt`-defect closure

Two further audit-identified defects, both addressed in a single dispatch.

### Defect 1 — `typFlatSize` outer bound under-saturation at deeply-nested types

**What was wrong**: `typFlatSize` / `dataTypeFlatSize` (and their concrete
sibling, plus `unflattenValue`) used `decls.size + 1` as the recursion bound.
The bound parameter is consumed at *both* `.ref`/`.app` cycle-walking depth
(one fresh `Global` inserted into `visited` per step, capped by `decls.size`)
AND syntactic descent through `.tuple` / `.array` arms. With a syntactically-
deep type like `data T = ctor (.tuple [.tuple [.tuple [.field]]])` and
`decls.size = 1`, the bound exhausts at the second nesting level, so
`typFlatSize` returns 0 — different from a generously-bounded run. This
breaks the saturation chain in `#5sat`: the bridge to `Concrete.DataType.size`
(which uses an `Except` monad with thrown errors instead of a 0-default) can
fail to compose because the typed-side and source-side outer bounds aren't
both above the saturation threshold.

**What was changed**:

1. **Added `Aiur.Typ.depth : Typ → Nat`** in `Ix/Aiur/Stages/Source.lean`,
   structured-recursive on `sizeOf` (using `Array.attach.foldl` + `List.foldl`
   for `tuple` / `function`-input recursion, mirroring the `Typ.beq` pattern).
   Returns 1 for non-recursive arms (`unit`, `field`, `pointer _`, `ref _`,
   `app _ _`, `mvar _`); `1 + max-of-children` for `tuple ts` /
   `function ins out` and `1 + child` for `array t _`.

2. **Added `Aiur.Source.Decls.maxTypDepth : Source.Decls → Nat`** in the
   same file. Iterates over every `(_, decl)` pair in `decls.pairs` and
   takes the `Typ.depth`-max over every `argTypes` (constructor / function-
   input) and every `output` typ.

3. **Updated outer wrappers** in `Ix/Aiur/Semantics/Flatten.lean`:
   - `typFlatSize` and `dataTypeFlatSize` now use bound
     `decls.size + decls.maxTypDepth + 1`.
   - `unflattenValue` mirrors the same widening.
   - Concrete-side `Concrete.dataTypeFlatSize` left at `decls.size + 1`
     because `Concrete.Decls` is post-monomorphization (no `.app`/`.mvar`,
     all dts are mono); a parallel `Concrete.Decls.maxTypDepth` could be
     added if/when concrete-side saturation chains uncover the same issue.

4. **Updated #5sat sig** in `Ix/Aiur/Proofs/ConcretizeSound/Layout.lean` to
   reference the widened bound:
   ```
   dataTypeFlatSizeBound decls (decls.size + decls.maxTypDepth + 1) {} dt = n
   ```
   (was `decls.size + 1`). The lemma body is unchanged; the bundled BLOCKED
   sub-leaves (`BLOCKED-dtFlatSize-mono-source-step`,
   `BLOCKED-dtFlatSize-mono-concrete`, `BLOCKED-dtFlatSize-bridge-perArgEq`,
   `BLOCKED-dtFlatSize-matched-bridge`) now have access to a syntactically-
   sufficient outer bound, removing the structural blocker on the source-side
   monotonicity argument.

**Cascade points**:

- `Ix/Aiur/Stages/Source.lean`: `Typ.depth` + `Source.Decls.maxTypDepth`
  added.
- `Ix/Aiur/Semantics/Flatten.lean`: 3 outer wrappers updated (`typFlatSize`,
  `dataTypeFlatSize`, `unflattenValue`); docstring refreshed to explain the
  two-summand bound (cycle-walk + syntactic-depth).
- `Ix/Aiur/Proofs/ConcretizeSound/Layout.lean:1820-1824`: `#5sat` sig
  updated; body unchanged.
- All consumers that wrote `decls.size + 1` literally in proof sigs are
  unaffected — those references are in **comments only** (per the audit
  grep `decls\.size \+ 1` in `Ix/Aiur/`). The proof-relevant consumers go
  through the outer-wrapper definitions (`typFlatSize` / `dataTypeFlatSize`
  / `dataTypeFlatSize_eq_layoutMap_size_wf`) which automatically pick up
  the new bound via def-unfolding.

**Files touched**: 3 (`Source.lean`, `Flatten.lean`,
`ConcretizeSound/Layout.lean`).
**Sorry count delta**: 0 (the amendment removes a structural blocker on
the analytical sub-leaf without itself being a new sorry).
**Build status**: green.

### Defect 2 — `Typed.Term.RefsDt.ref` arm A.ctor structural incompatibility

**What was wrong**: at `concretize_preserves_TermRefsDt`'s bridge body
(`Ix/Aiur/Proofs/ConcretizeSound/TermRefsDtBridge.lean`), Arm A.ctor (typed
body has `.ref g` with `tArgs.isEmpty` and `g` keyed `.constructor dt c`)
needed `dt.params = []` to apply
`PhaseA2.concretizeBuild_preserves_ctor_kind_fwd` (CtorKind.lean:422). But
the source-side `Typed.Term.RefsDt.ref` predicate's premise was just
`∃ dt c, tds[g] = .constructor dt c` — no params constraint. Polymorphic
ctors with `dt.params != []` and `tArgs.isEmpty` cannot arise from
`refLookup` (Check.lean:421-441 — mono case at line 435-436 emits
`tArgs = #[]` only when `dt.params.isEmpty`; poly case at line 437-439
emits `tArgs.size = dt.params.length > 0`), so the case is structurally
unreachable from typed bodies — but the predicate over-approximated and
admitted it.

**What was changed**:

1. **Amended `Aiur.Typed.Term.RefsDt.ref`** (`Ix/Aiur/Semantics/WellFormed.lean:185+`):
   ```
   | ref   {typ e g tArgs}
       (hdt : ∃ dt c, tds.getByKey g = some (.constructor dt c) ∧
         (dt.params.isEmpty ∨ ¬ tArgs.isEmpty)) :
       RefsDt tds (.ref typ e g tArgs)
   ```
   The new disjunct rules out the structurally-impossible
   `tArgs.isEmpty ∧ dt.params.length > 0` shape.

2. **Updated `substInTypedTerm_preserves_RefsDt`** (`FirstOrder.lean:1361+`)
   to thread the disjunct: substitution preserves `tArgs.size` (via
   `tArgs.map`), so `.isEmpty` transports verbatim.

3. **Updated `rewriteTypedTerm_preserves_RefsDt`** (`RefsDt.lean:40+`)
   bridge premise:
   ```
   hbridge : ∀ g tArgs,
     (∃ dt c, decls.getByKey g = some (.constructor dt c) ∧
       (dt.params.isEmpty ∨ ¬ tArgs.isEmpty)) →
     ∃ dt c, tds'.getByKey (rewriteGlobal decls mono g tArgs) =
       some (.constructor dt c) ∧
       (dt.params.isEmpty ∨ ¬ (tArgs.map (rewriteTyp subst mono)).isEmpty)
   ```

4. **Updated `concretizeBuild_preserves_TermRefsDt`** (`TermRefsDtBridge.lean:58+`)
   bridge premise: same shape with the substitution pinned to `emptySubst`
   (`fun _ => none`) to match `concretizeBuild_function_origin_with_body`'s
   call pattern.

5. **Updated `termToConcrete_preserves_RefsDt`** (`RefsDt.lean:572+`):
   the concrete-side `Concrete.Term.RefsDt.ref` predicate doesn't carry
   the disjunct (concrete-side has no `params`-bearing source-style dt),
   so we strip it via destructuring before applying `hwit`.

6. **Updated bridge dispatch** in `concretize_preserves_TermRefsDt`
   (`TermRefsDtBridge.lean:171+`):
   - **Arm A.ctor (`tArgs.isEmpty`)**: now extracts `dt.params = []` from
     the new disjunct (since `tArgs.isEmpty` rules out `Or.inr`). Applies
     `PhaseA2.concretizeBuild_preserves_ctor_kind_fwd`. Output disjunct
     discharges via `Or.inl md_dt.params.isEmpty` (still BLOCKED on
     params-preservation through kind-fwd; see new sub-sorry below).
   - **Arms B/C/D (`tArgs.nonempty`)**: output disjunct discharges trivially
     via `Or.inr` since `tArgs.map`-rewriting preserves `.size` (and hence
     `.isEmpty`), captured in the helper `htArgs_isEmpty_iff`.

**New BLOCKED sub-sorries planted**:

The Arm A.ctor closure now has 3 granular leaves (was 1 monolithic
`BLOCKED-RefsDt-Bridge-A-ctor`):

- `BLOCKED-RefsDt-Bridge-A-disjoint`: discharge `hDtNotKey` /
  `hFnNotKey` (no `dt' ∈ drained.newDataTypes` / `f ∈ drained.newFunctions`
  collides with `g = dt.name.pushNamespace c.nameHead`). Closure pattern
  parallels Arm D's disjointness — express the source ctor key as
  `concretizeName _ #[singletonRefArg]` (single-limb) and apply
  `ConcretizeUniqueNames` (which is in scope via `hUnique`). ~80 LoC each
  (mirror of Arm D's pattern in `SizeBound.lean:1715-1820`).
- `BLOCKED-RefsDt-Bridge-A-md-params`: extract `md_dt.params = []` from
  `concretizeBuild_preserves_ctor_kind_fwd`. The post-fold ctor's parent
  dt has structure `{ td_dt with constructors := rewrittenCtors }` (per
  `fromSource_inserts_ctor_at_key_explicit` in `CtorKind.lean:813`),
  preserving `params`. Threading the explicit-variant's result up to
  the outer `_fwd`'s existential is ~30 LoC of structural plumbing.

The original `BLOCKED-RefsDt-Bridge-A-ctor` is now CLOSED at the
"structural-incompatibility" level: Arm A.ctor compiles and applies
kind-fwd; the remaining work is purely the disjointness side conditions
(parallel to Arm D's existing leaf) plus the params-preservation
discharge. 

**Cascade points**:

- `Ix/Aiur/Semantics/WellFormed.lean:185+`: predicate amended.
- `Ix/Aiur/Proofs/ConcretizeSound/FirstOrder.lean:1368-1390`:
  `substInTypedTerm_preserves_RefsDt` `.ref` arm threads the new disjunct.
- `Ix/Aiur/Proofs/ConcretizeSound/RefsDt.lean:40-65`:
  `rewriteTypedTerm_preserves_RefsDt` bridge premise reshape.
- `Ix/Aiur/Proofs/ConcretizeSound/RefsDt.lean:603-620`:
  `termToConcrete_preserves_RefsDt` `.ref` arm strips disjunct.
- `Ix/Aiur/Proofs/ConcretizeSound/TermRefsDtBridge.lean:58-90`:
  `concretizeBuild_preserves_TermRefsDt` bridge premise reshape.
- `Ix/Aiur/Proofs/ConcretizeSound/TermRefsDtBridge.lean:218-388`:
  consumer `concretize_preserves_TermRefsDt`'s `hRefsBridge` body — Arm A
  reworked to extract `dt.params = []` and apply kind-fwd.

**Files touched**: 4 (`WellFormed.lean`, `FirstOrder.lean`, `RefsDt.lean`,
`TermRefsDtBridge.lean`).
**Sorry count**: 9 → 9 (Arm A's monolithic blocker decomposed into 3
granular sub-sorries inside the same outer theorem).
**Build status**: green; CheckReach clean.
