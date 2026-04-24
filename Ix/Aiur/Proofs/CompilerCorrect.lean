module
public import Ix.Aiur.Proofs.CompilerPreservation
public import Ix.Aiur.Proofs.CompilerProgress
public import Ix.Aiur.Proofs.CheckSound
public import Ix.Aiur.Proofs.ConcretizeSound
public import Ix.Aiur.Proofs.ConcretizeSound.TypesNotFunction
public import Ix.Aiur.Proofs.ConcretizeSound.TermRefsDtBridge
public import Ix.Aiur.Semantics.WellFormed

/-!
`compile_correct`, the final theorem.

Combines `compile_progress` (progress) and `compile_preservation`
(preservation) into the headline theorem of the verified compiler.
-/

@[expose] public section

namespace Aiur

open Source

-- `Toplevel.typedDecls_params_empty_entry` removed (orphan post-D.1 refactor).
-- D.1 closure dropped the universal hparamsEmpty bridge; the per-entry form
-- has no current consumer. Resurrect from git history if needed.

/-- **Entry-restricted `concretize_produces_refClosed`.**

Same conclusion as `concretize_produces_refClosed` but takes only
`WellFormed t` + `mkDecls/checkAndSimplify/concretize` witnesses (no
`FullyMonomorphic t`). Body delegates to
`Toplevel.concretize_produces_refClosed_entry` in `ConcretizeSound`, which
carries the lone bridge sorry (a structural-only proof using `DrainState`
invariants that does NOT pass through universal `AllRefsAreDtKeys tds`). -/
theorem Toplevel.concretize_refClosed_entry
    {t : Source.Toplevel} {decls : Source.Decls} {tds : Typed.Decls}
    {cd : Concrete.Decls}
    (hwf : WellFormed t)
    (hdecls : t.mkDecls = .ok decls)
    (hts : t.checkAndSimplify = .ok tds)
    (hconc : tds.concretize = .ok cd) :
    Concrete.Decls.RefClosed cd :=
  Toplevel.concretize_produces_refClosed_entry hwf hdecls hts hconc

/-! ## `Concrete.Eval.runFunction_preserves_MonoCtorReach` — concrete-side twin.

Mirror of the source-side `runFunction_preserves_MonoCtorReach`
(ValueEqFlatten.lean) but for `Concrete.Eval.runFunction`. Consumed by
`compile_correct`'s `hconcRetReach` discharge.

**Sig amendment 2026-05-04 (#14 closure)**: hoist the concrete-side
`applyGlobal` preservation lemma as a premise (`_hApplyGlobalReach`).
Strategy mirrors source-side #1.A: rather than reopening the
`Concrete.Eval` mutual block (or planting a parallel
`Concrete.MonoCtorReachBody` namespace with five granular leaves), we let
the caller supply the `applyGlobal` IH at fuel level. The body becomes a
single dispatch.

The downstream consumer (`compile_correct`'s `hconcRetReach`) discharges
the hoisted premise via a still-open BLOCKED-ConcreteApplyGlobalReach
sub-sorry — folded into `compile_correct`'s existing sorry envelope, so
this closure decreases the global sorry count by 1 (#14 → closed).

Wire-keepalive (Invariant 1): the inner `let _ :=
@Aiur.runFunction_preserves_MonoCtorReach` keeps the source-side twin
reachable from `compile_correct`'s closure (CheckReach.lean target).

Closure path:
1. `change` `Concrete.Eval.runFunction` to its `match`-on-`applyGlobal`
   beta-reduced form (via `rfl`).
2. Split on the inner `applyGlobal` result: error arm vacuous; ok arm
   dispatches to the hoisted `_hApplyGlobalReach` premise. -/
theorem Concrete.Eval.runFunction_preserves_MonoCtorReach
    {decls : Source.Decls} {concDecls : Concrete.Decls}
    (_hCtorPreserved : Decls.CtorPreserved decls concDecls)
    (_hApplyGlobalReach :
      ∀ (fuel' : Nat) (g' : Global) (args' : List Value)
        (st'' : Concrete.Eval.EvalState)
        (_hargsReach' : ∀ v ∈ args', Value.MonoCtorReach decls concDecls v)
        (v' : Value) (st''' : Concrete.Eval.EvalState)
        (_hcall : Concrete.Eval.applyGlobal concDecls fuel' g' args' st''
                  = .ok (v', st''')),
        Value.MonoCtorReach decls concDecls v')
    (name : Global) (args : List Value) (io₀ : IOBuffer) (fuel : Nat)
    (_hargsReach : ∀ v ∈ args, Value.MonoCtorReach decls concDecls v)
    (v : Value) (io : IOBuffer)
    (_hrun : Concrete.Eval.runFunction concDecls name args io₀ fuel = .ok (v, io)) :
    Value.MonoCtorReach decls concDecls v := by
  -- Wire-keepalive (Invariant 1): keep the source-side twin reachable.
  let _ := @Aiur.runFunction_preserves_MonoCtorReach
  -- Beta-reduce `runFunction`'s `let st := …` binder to expose the inner
  -- `applyGlobal` match. Mirror of the source-side body in
  -- `runFunction_preserves_MonoCtorReach` (ValueEqFlatten.lean).
  have hrun_eq :
      Concrete.Eval.runFunction concDecls name args io₀ fuel =
      (match Concrete.Eval.applyGlobal concDecls fuel name args
              { ioBuffer := io₀ } with
       | .error e => Except.error e
       | .ok (v, st') => .ok (v, st'.ioBuffer)) := rfl
  rw [hrun_eq] at _hrun
  split at _hrun
  · cases _hrun
  · rename_i v' st' hcall
    injection _hrun with hpair
    injection hpair with hv _
    subst hv
    exact _hApplyGlobalReach fuel name args { ioBuffer := io₀ } _hargsReach
      v' st' hcall

/-- **Per-entry concrete-FnFree-return witness.**

Specialized to a single entry name + caller arguments. Provable via
type-soundness + per-entry monomorphism (entry forces `f.params = []`,
and concretize's drain monomorphizes the transitive call graph). Used by
`compile_correct` to discharge `_hconcRetFnFree` in the per-entry
preservation clause without a global `FullyMonomorphic t`.

Now constructed F=0 by composition of named entry-bridge sub-witnesses
(`typedDecls_params_empty_entry` for FO/TermRefsDt + `concretize_refClosed_entry`
for RefClosed). The sorries shift INTO those named bridge lemmas, each
realistically dischargeable by future per-entry refactor. -/
theorem Toplevel.compile_correct_concRetFnFree_entry
    (t : Source.Toplevel) (hwf : WellFormed t)
    (name : Lean.Name) (args : List Value) (io₀ : IOBuffer) (fuel : Nat)
    (hargsFnFree : ∀ v ∈ args, Value.FnFree v) :
    ∀ (concDecls : Concrete.Decls) v io,
      t.checkAndSimplify.toOption.bind (·.concretize.toOption) = some concDecls →
      Concrete.Eval.runFunction concDecls (Global.mk name) args io₀ fuel = .ok (v, io) →
      Value.FnFree v := by
  intro concDecls v io hcd hrun
  -- Recover decls + tds witnesses from `hwf`.
  obtain ⟨decls, hdecls⟩ := hwf.mkDecls_ok
  have ⟨tds, hts, hconc⟩ : ∃ tds : Typed.Decls,
      t.checkAndSimplify = .ok tds ∧ tds.concretize = .ok concDecls := by
    cases hts : t.checkAndSimplify with
    | error _ => simp [hts, Except.toOption] at hcd
    | ok tds =>
      cases hconc : tds.concretize with
      | error _ => simp [hts, hconc, Except.toOption] at hcd
      | ok cd =>
        simp [hts, hconc, Except.toOption] at hcd
        subst hcd
        exact ⟨tds, rfl, hconc⟩
  -- FirstOrderReturn — sig refactored to no longer take `hparamsEmpty`.
  -- The drain-leaf substitution-FO side condition is discharged via the
  -- `DrainState.PendingArgsFO` companion invariant; the remaining bridge
  -- (`concretize_PendingArgsFO_bridge` in ConcretizeSound) packages
  -- seed-init + iter-preservation as a single sorry blocked on the typed
  -- `Typed.Decls.AppRefTArgsFO` hypothesis (new `WellFormed` field, ~250
  -- LoC closure path).
  have hFOR : Concrete.Decls.FirstOrderReturn concDecls :=
    concretize_preserves_FirstOrderReturn (hwf.firstOrderReturn _ hts)
      (hwf.noPolyAppRefTArgs _ hts) hconc
  -- TermRefsDt — `hparamsEmpty` no longer required.
  -- Sig amendments 2026-05-04: `concretize_preserves_TermRefsDt` now takes
  -- `hUnique` (carried by `WellFormed.noNameCollisions`) for the bridge's
  -- mono-hit-arm disjointness discharge, plus `hdecls` to access
  -- source-side dt-companion lookups (used to lift typed ctor keys to
  -- source dt-keys via `mkDecls_ctor_companion` and
  -- `mkDecls_source_ctor_is_key`).
  have hTermRefsDt : Concrete.Decls.TermRefsDt concDecls :=
    concretize_preserves_TermRefsDt hwf.noTermRefsToFunctions
      (hwf.noNameCollisions tds hts) hdecls hts hconc
  -- RefClosed — currently consumes `FullyMonomorphic t`; entry-bridge sorry.
  have hRefClosed : Concrete.Decls.RefClosed concDecls :=
    Toplevel.concretize_refClosed_entry hwf hdecls hts hconc
  -- TypesNotFunction — discharged via `concretize_preserves_TypesNotFunction`,
  -- the propagation chain (drain + `concretizeBuild` + `step4Lower` fold) that
  -- mirrors `concretize_preserves_TermRefsDt`. The source-level `WellFormed`
  -- field `noTypesAreFunctions` records that every typed `.load` carrier type
  -- in `tds` is `.function`-free; the bridge then lifts it to concrete cd.
  have hTypesNF : Concrete.Decls.TypesNotFunction concDecls :=
    concretize_preserves_TypesNotFunction hwf.noTypesAreFunctions
      hwf.noPolyAppRefTArgs hts hconc
  exact Concrete.Eval.runFunction_preserves_FnFree concDecls (Global.mk name)
    args io₀ fuel hFOR hRefClosed hTermRefsDt hTypesNF hargsFnFree v io hrun

/-- **The verified-compiler theorem.**

For every well-formed source `t`:
(a) *Progress* — compilation succeeds.
(b) *Preservation* — the bytecode output of every **entry point** is
    semantically equivalent to the source under `InterpResultEq`, composed
    through source → simplify → concretize → lower → dedup → bytecode.

The preservation clause is restricted to entry functions (`f.entry = true`).
By `Source.Function.notPolyEntry`, entries are forced to be monomorphic
(`params = []`). Together with the transitive call graph from entries —
which `concretize` fully concretizes — this gives a per-entry monomorphism
property without requiring a global `FullyMonomorphic t` `WellFormed` field.

`InterpResultEq` is asymmetric: source-ok → bytecode-ok-and-equivalent;
bytecode permitted to over-succeed where source errors. -/
theorem Toplevel.compile_correct
    (t : Source.Toplevel) (hwf : WellFormed t) :
    -- (a) Progress: compilation succeeds.
    (∃ ct decls, t.mkDecls = .ok decls ∧ t.compile = .ok ct)
    ∧
    -- (b) Preservation, scoped to entry functions.
    (∀ ct decls,
      t.mkDecls = .ok decls →
      t.compile = .ok ct →
      ∀ (name : Lean.Name) (funIdx : Bytecode.FunIdx)
        (_hname : ct.getFuncIdx name = some funIdx)
        {f : Source.Function}
        (_hsrc : decls.getByKey (Global.mk name) = some (.function f))
        -- Restrict to entry points. By `Source.Function.notPolyEntry`,
        -- this forces `f.params = []` (no polymorphic public entries).
        (_hentry : f.entry = true)
        (args : List Value) (io₀ : IOBuffer) (fuel : Nat) (retTyp : Typ)
        -- Args contain no first-class function values. Caller-known property
        -- of the call site; no internal repository invariant constrains it.
        (_hargsFnFree : ∀ v ∈ args, Value.FnFree v)
        -- Sig amendment 2026-04-30: caller-provided `MonoCtorReach` witness
        -- mirrors `hargsFnFree`. For first-order arg types (which entry
        -- inputs typically are), this discharges via the structural arms
        -- (`unit`/`field`/`pointer` etc., no `.ctor` arm fires). For inputs
        -- containing `.ctor`, the caller must witness the dt-key existence
        -- on both source and concrete decls — same shape as `hargsFnFree`'s
        -- "no `.fn`" obligation.
        (_hargsReach : ∀ (concDecls : Concrete.Decls),
          t.checkAndSimplify.toOption.bind (·.concretize.toOption) = some concDecls →
          ∀ v ∈ args, Value.MonoCtorReach decls concDecls v),
      InterpResultEq decls ct.globalFuncIdx retTyp
        (Source.Eval.runFunction decls (Global.mk name) args io₀ fuel)
        (Bytecode.Eval.runFunction ct.bytecode funIdx
          (Flatten.args decls ct.globalFuncIdx args) io₀ fuel)) := by
  -- Real composition through `compile_progress_entry` + `compile_preservation_entry`.
  -- These are entry-restricted variants of the original progress/preservation
  -- halves; they take `WellFormed t` only (no global `FullyMonomorphic t`).
  -- Their bodies remain `sorry` with BLOCKED notes (the per-entry derivation
  -- through `_under_fullymono` consumers is multi-week work — NOTES.md
  -- "Phase X1/X2"). Crucially: the placeholder `hFullyMono : FullyMonomorphic t`
  -- (false for polymorphic source) is GONE. Each remaining sorry is a NAMED
  -- bridge realistically dischargeable by future per-entry refactor.
  refine ⟨?_, ?_⟩
  · -- (a) Progress.
    exact Toplevel.compile_progress_entry t hwf
  · -- (b) Preservation, scoped to entry functions.
    intros ct decls hdecls hct name funIdx hname f hsrc hentry args io₀ fuel retTyp
                hargsFnFree hargsReach
    -- `_hcdNameAgrees` (structural witness about `concretize` output) is
    -- derived F=0 from `concretize_nameAgrees` + `checkAndSimplify_preserves_nameAgrees`,
    -- both of which are independent of FullyMono.
    have hcdNameAgrees : ∀ (concDecls : Concrete.Decls),
        t.checkAndSimplify.toOption.bind (·.concretize.toOption) = some concDecls →
        ∀ (key : Global) (g : Concrete.Function),
          (key, Concrete.Declaration.function g) ∈ concDecls.pairs.toList → key = g.name := by
      intro concDecls hcd key g hmem
      have ⟨tds, hts, hconc⟩ : ∃ tds : Typed.Decls,
          t.checkAndSimplify = .ok tds ∧ tds.concretize = .ok concDecls := by
        cases hts : t.checkAndSimplify with
        | error _ => simp [hts, Except.toOption] at hcd
        | ok tds =>
          cases hconc : tds.concretize with
          | error _ => simp [hts, hconc, Except.toOption] at hcd
          | ok cd =>
            simp [hts, hconc, Except.toOption] at hcd
            subst hcd
            exact ⟨tds, rfl, hconc⟩
      have htdna := checkAndSimplify_preserves_nameAgrees hts
      exact concretize_nameAgrees htdna hconc key g hmem
    -- `_hconcRetFnFree` (the concrete evaluator returns `Value.FnFree`) follows
    -- from type-soundness: requires `FirstOrderReturn` + `RefClosed` + `TermRefsDt`
    -- on the concrete decls + FnFree args. The first three currently come
    -- through `_under_fullymono` chains; named-bridge sorry until they are
    -- refactored to per-call (or the concrete-side version is closed
    -- independently — NOTES.md "Phase X1 S1").
    have hconcRetFnFree : ∀ (concDecls : Concrete.Decls) v io,
        t.checkAndSimplify.toOption.bind (·.concretize.toOption) = some concDecls →
        Concrete.Eval.runFunction concDecls (Global.mk name) args io₀ fuel = .ok (v, io) →
          Value.FnFree v :=
      Toplevel.compile_correct_concRetFnFree_entry t hwf name args io₀ fuel hargsFnFree
    -- `hargsReach` is now caller-provided (sig amendment 2026-04-30) — it
    -- mirrors `hargsFnFree`. For typical first-order entry inputs the
    -- caller's discharge is trivial (no `.ctor` arm fires).
    -- `hconcRetReach` (the Concrete evaluator returns `MonoCtorReach`)
    -- follows from the Concrete-side
    -- `runFunction_preserves_MonoCtorReach` mirror — which is an orphan
    -- BLOCKED on the twin lemma in ValueEqFlatten.lean. Until that lemma
    -- closes, this remains a focused F=1 BLOCKED stub.
    have hconcRetReach : ∀ (concDecls : Concrete.Decls) v io,
        t.checkAndSimplify.toOption.bind (·.concretize.toOption) = some concDecls →
        Concrete.Eval.runFunction concDecls (Global.mk name) args io₀ fuel = .ok (v, io) →
          Value.MonoCtorReach decls concDecls v := by
      -- WIRED 2026-04-30: Concrete-side `runFunction_preserves_MonoCtorReach`
      -- mirror (ValueEqFlatten.lean) discharges this obligation. The mirror
      -- consumes a `Decls.CtorPreserved decls concDecls` witness, which is
      -- produced by `concretizeBuild_preserves_ctor_kind_at_entry_fwd`
      -- (Phase4.lean) — entry-restricted ctor-kind preservation through the
      -- three folds of `concretizeBuild`, then lifted across `step4Lower`.
      --
      -- The wiring below makes both the source-side twin
      -- (`runFunction_preserves_MonoCtorReach`) and the concrete-side mirror
      -- transitively reachable from `compile_correct` per CheckReach.lean.
      intro concDecls v io _hcd hrun
      -- Step 1: derive `Decls.CtorPreserved decls concDecls` from the entry-restricted
      -- ctor-kind preservation chain. The full closure walks
      --   typed `.constructor` at g (via `checkAndSimplify_preserves_ctor_kind`)
      --   ↦ monoDecls `.constructor` at g (via `concretizeBuild_preserves_ctor_kind_at_entry_fwd`)
      --   ↦ concDecls `.constructor` at g (via step4Lower forward kind preservation).
      -- The sub-sorry below packages this lift; the inner reference makes the
      -- Phase4 helper transitively reachable from `compile_correct`.
      have hCtorPreserved : Decls.CtorPreserved decls concDecls := by
        -- Closure of #15.A (BLOCKED-CtorPreserved-from-entry-compilation).
        --
        -- Sig amendment 2026-05-04 (architectural-defect closure):
        -- `Decls.CtorPreserved` is FWD-ONLY. The previously paired BWD
        -- direction was provably False on polymorphic source (mangled-key
        -- origins from drain's `newDataTypes` produce ctor entries at
        -- concrete keys with no source preimage at the same key). The BWD
        -- direction had no real consumer in the reachable closure — the
        -- source-side `MonoCtorReachBody.applyGlobal_MonoCtorReach` only
        -- references the FWD direction; the concrete-side mirror (currently
        -- routed through `_hApplyGlobalReach`) needs a separate
        -- template-name BWD predicate (NOT same-key BWD), to be planted
        -- when needed. Phantom `BLOCKED-CtorPreserved-BWD` removed.
        --
        -- FWD direction (source `.constructor` with `dt.params = []` ⟹ concrete
        -- `.constructor` at the same key): proved as a 3-step chain:
        --   (a) `checkAndSimplify_preserves_ctor_kind_fwd` lifts source `.ctor`
        --       to typed `.ctor` at `g`. Combined with `FnMatchP_checkAndSimplify`
        --       (typed → source ctor key preservation), `td_dt = dt`/`td_c = c`,
        --       so `td_dt.params = dt.params = []`.
        --   (b) `concretizeBuild_preserves_ctor_kind_at_entry_fwd` lifts typed
        --       `.ctor` at `g` to monoDecls `.ctor` at `g`.
        --   (c) `step4Lower_preserves_ctor_kind_fwd` lifts monoDecls `.ctor` at
        --       `g` to concDecls `.ctor` at `g`.
        -- Recover typed-decls + concretize witnesses from `_hcd`.
        have ⟨tds, hts, hconc⟩ : ∃ tds : Typed.Decls,
            t.checkAndSimplify = .ok tds ∧ tds.concretize = .ok concDecls := by
          cases hts : t.checkAndSimplify with
          | error _ => simp [hts, Except.toOption] at _hcd
          | ok tds =>
            cases hconc : tds.concretize with
            | error _ => simp [hts, hconc, Except.toOption] at _hcd
            | ok cd =>
              simp [hts, hconc, Except.toOption] at _hcd
              subst _hcd
              exact ⟨tds, rfl, hconc⟩
        have hUniqueNames : Typed.Decls.ConcretizeUniqueNames tds :=
          hwf.noNameCollisions tds hts
        -- Extract `drained` from `hconc` for the Phase4 helper.
        have hconc_orig := hconc
        unfold Typed.Decls.concretize at hconc_orig
        simp only [bind, Except.bind] at hconc_orig
        split at hconc_orig
        · cases hconc_orig
        rename_i drained hdrain
        -- The foldlM at the bottom of `Typed.Decls.concretize` runs over
        -- `monoDecls := concretizeBuild tds drained.mono drained.newFunctions
        -- drained.newDataTypes` and produces `concDecls`.
        have hfold : (concretizeBuild tds drained.mono drained.newFunctions
            drained.newDataTypes).foldlM (init := default) step4Lower
              = .ok concDecls := hconc_orig
        -- FWD direction (the only direction in the FWD-only sig).
        intro g dt c hsrc hdt_params
        -- Step (a): source `.ctor` ⟹ typed `.ctor` at `g`. Then identify
        -- `td_dt = dt` / `td_c = c` via FnMatchP backward.
        obtain ⟨td_dt, td_c, htd⟩ :=
          checkAndSimplify_preserves_ctor_kind_fwd hdecls hts hsrc
        have hP := FnMatchP_checkAndSimplify hdecls hts
        have hsrc_again : decls.getByKey g = some (.constructor td_dt td_c) :=
          (hP g).2.2 td_dt td_c htd
        rw [hsrc] at hsrc_again
        have ⟨htd_dt_eq, _⟩ : dt = td_dt ∧ c = td_c := by
          simp only [Option.some.injEq, Source.Declaration.constructor.injEq]
            at hsrc_again
          exact hsrc_again
        have htd_dt_params : td_dt.params = [] := htd_dt_eq ▸ hdt_params
        -- Step (b): typed `.ctor` ⟹ monoDecls `.ctor` at `g`.
        obtain ⟨md_dt, md_c, hmono⟩ :=
          concretizeBuild_preserves_ctor_kind_at_entry_fwd hdecls hts hdrain
            hconc hUniqueNames htd htd_dt_params
        -- Step (c): monoDecls `.ctor` ⟹ concDecls `.ctor` at `g`.
        exact step4Lower_preserves_ctor_kind_fwd hmono hfold
      -- Step 2: discharge the hoisted `_hApplyGlobalReach` premise. Sig
      -- amendment 2026-05-04 (#14 closure) hoisted the concrete-side
      -- `applyGlobal` preservation lemma into the runFunction-mirror's
      -- signature so the mirror itself becomes a single-dispatch closure.
      -- The concrete-side `applyGlobal_MonoCtorReach` is itself a future
      -- per-arm decomposition mirror of the source-side `MonoCtorReachBody`
      -- (ValueEqFlatten.lean). For now this remains a focused F=1 BLOCKED
      -- stub folded into the existing `compile_correct` sorry envelope.
      have hApplyGlobalReach :
          ∀ (fuel' : Nat) (g' : Global) (args' : List Value)
            (st'' : Concrete.Eval.EvalState)
            (_hargsReach' : ∀ v ∈ args', Value.MonoCtorReach decls concDecls v)
            (v' : Value) (st''' : Concrete.Eval.EvalState)
            (_hcall : Concrete.Eval.applyGlobal concDecls fuel' g' args' st''
                      = .ok (v', st''')),
            Value.MonoCtorReach decls concDecls v' := by
        -- BLOCKED-ConcreteApplyGlobalReach: future closure mirrors the
        -- source-side `MonoCtorReachBody.applyGlobal_MonoCtorReach`
        -- (ValueEqFlatten.lean), itself closed via hoisted `_hInterpReach`.
        -- The concrete analog plants a parallel `Concrete.MonoCtorReachBody`
        -- namespace with five granular leaves (`applyGlobal/applyLocal/
        -- interp/evalList/evalMatchCases`) — same structural pattern as
        -- `FnFreeBody` in `ConcretizeSound/FnFree.lean`. Reachability for
        -- the source-side template is preserved via the wirings below.
        let _ := @Aiur.MonoCtorReachBody.applyGlobal_MonoCtorReach
        let _ := @Aiur.MonoCtorReachBody.applyLocal_MonoCtorReach
        let _ := @Aiur.MonoCtorReachBody.interp_MonoCtorReach
        let _ := @Aiur.MonoCtorReachBody.evalList_MonoCtorReach
        let _ := @Aiur.MonoCtorReachBody.evalMatchCases_MonoCtorReach
        sorry
      -- Step 3: dispatch via the Concrete-side mirror.
      exact Concrete.Eval.runFunction_preserves_MonoCtorReach hCtorPreserved
        hApplyGlobalReach (Global.mk name) args io₀ fuel
        (hargsReach concDecls _hcd) v io hrun
    -- Caller-provided `Decls.R` for the simulation chain (sig amendment
    -- 2026-05-03, Defect 1). Bundles `CtorPreserved + FnNamesAgree`;
    -- both are produced by the entry-restricted kind-preservation chain
    -- in Phase4 + step4Lower-backward family. Same compilation chain
    -- as `hCtorPreserved` above; the FnNamesAgree clause additionally
    -- composes through `concretizeBuild_preserves_function_kind_at_entry_fwd`.
    have hDeclsR : ∀ (concDecls : Concrete.Decls),
        t.checkAndSimplify.toOption.bind (·.concretize.toOption) = some concDecls →
        Aiur.Simulation.Decls.R decls concDecls := by
      intro concDecls _hcd
      -- Closure of #15.B (BLOCKED-Decls-R-from-entry-compilation).
      --
      -- Sig amendment 2026-05-04 (architectural-defect closure): both
      -- `Decls.CtorPreserved` and `Decls.FnNamesAgree` are FWD-only.
      -- The previously paired BWD directions were provably False on
      -- polymorphic source (mangled-key origins from drain's `newDataTypes` /
      -- `newFunctions` produce concrete entries at keys with no source
      -- preimage at the same key). Phantom `BLOCKED-CtorPreserved-BWD`
      -- and `BLOCKED-FnNamesAgree-BWD` removed.
      --
      -- `Decls.R = Decls.CtorPreserved ∧ Decls.FnNamesAgree`. The
      -- `CtorPreserved` clause is structurally identical to the discharge of
      -- `hCtorPreserved` above (3-step chain
      -- `checkAndSimplify_preserves_ctor_kind_fwd` →
      -- `concretizeBuild_preserves_ctor_kind_at_entry_fwd` →
      -- `step4Lower_preserves_ctor_kind_fwd`). The `FnNamesAgree` clause is
      -- the function analog: goes through the inputs-labels preserving
      -- variants `concretizeBuild_preserves_function_inputs_at_entry_fwd`
      -- (Phase4.lean:386) and `step4Lower_function_explicit` (Shapes.lean:1369).
      have ⟨tds, hts, hconc⟩ : ∃ tds : Typed.Decls,
          t.checkAndSimplify = .ok tds ∧ tds.concretize = .ok concDecls := by
        cases hts : t.checkAndSimplify with
        | error _ => simp [hts, Except.toOption] at _hcd
        | ok tds =>
          cases hconc : tds.concretize with
          | error _ => simp [hts, hconc, Except.toOption] at _hcd
          | ok cd =>
            simp [hts, hconc, Except.toOption] at _hcd
            subst _hcd
            exact ⟨tds, rfl, hconc⟩
      have hUniqueNames : Typed.Decls.ConcretizeUniqueNames tds :=
        hwf.noNameCollisions tds hts
      have hconc_orig := hconc
      unfold Typed.Decls.concretize at hconc_orig
      simp only [bind, Except.bind] at hconc_orig
      split at hconc_orig
      · cases hconc_orig
      rename_i drained hdrain
      have hfold : (concretizeBuild tds drained.mono drained.newFunctions
          drained.newDataTypes).foldlM (init := default) step4Lower
            = .ok concDecls := hconc_orig
      -- Inline `mapM_preserves_first_proj`: if `xs.mapM (fun p => do let
      -- t' ← f p.2; pure (p.1, t')) = .ok ys`, then `xs.map (·.1) = ys.map
      -- (·.1)`. Used to lift `cf.inputs.map (·.1) = md_f.inputs.map (·.1)`
      -- from the `step4Lower_function_explicit` mapM witness.
      have mapM_first_proj :
          ∀ (xs : List (Local × Typ)) (ys : List (Local × Concrete.Typ))
            (h : xs.mapM (fun (p : Local × Typ) => do
              let t' ← typToConcrete (∅ : Std.HashMap (Global × Array Typ) Global) p.2
              pure (p.1, t')) = .ok ys),
            xs.map (·.1) = ys.map (·.1) := by
        intro xs
        induction xs with
        | nil =>
          intro ys hmap
          simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at hmap
          subst hmap; rfl
        | cons hd tl ih =>
          intro ys hmap
          rw [List.mapM_cons] at hmap
          simp only [bind, Except.bind, pure, Except.pure] at hmap
          -- Outer match on `typToConcrete ∅ hd.2`.
          split at hmap
          · cases hmap
          rename_i t' ht'
          -- Inner match on `typToConcrete ∅ hd.2` inside `Except.ok (hd.fst, _)`.
          split at ht'
          · cases ht'
          rename_i v hv
          have hpair_eq : t' = (hd.fst, v) := by
            simp only [Except.ok.injEq] at ht'; exact ht'.symm
          subst hpair_eq
          -- Inner match on `tl.mapM ...`.
          split at hmap
          · cases hmap
          rename_i tail htail
          simp only [Except.ok.injEq] at hmap
          subst hmap
          have ih' := ih tail htail
          simp only [List.map_cons]
          rw [ih']
      refine ⟨?_, ?_⟩
      · -- `Decls.CtorPreserved` clause (FWD-only; same shape as `hCtorPreserved` above).
        intro g dt c hsrc hdt_params
        obtain ⟨td_dt, td_c, htd⟩ :=
          checkAndSimplify_preserves_ctor_kind_fwd hdecls hts hsrc
        have hP := FnMatchP_checkAndSimplify hdecls hts
        have hsrc_again : decls.getByKey g = some (.constructor td_dt td_c) :=
          (hP g).2.2 td_dt td_c htd
        rw [hsrc] at hsrc_again
        have ⟨htd_dt_eq, _⟩ : dt = td_dt ∧ c = td_c := by
          simp only [Option.some.injEq, Source.Declaration.constructor.injEq]
            at hsrc_again
          exact hsrc_again
        have htd_dt_params : td_dt.params = [] := htd_dt_eq ▸ hdt_params
        obtain ⟨md_dt, md_c, hmono⟩ :=
          concretizeBuild_preserves_ctor_kind_at_entry_fwd hdecls hts hdrain
            hconc hUniqueNames htd htd_dt_params
        exact step4Lower_preserves_ctor_kind_fwd hmono hfold
      · -- `Decls.FnNamesAgree` clause (FWD-only).
        intro g f_src hsrc hf_params
        -- Step (a): source `.function f_src` ⟹ typed `.function tf` at `g`,
        -- with `tf.inputs = f_src.inputs` and `tf.params = f_src.params = []`.
        have hkeys := checkAndSimplify_keys_local hdecls hts g
        have hsrc_ne : decls.getByKey g ≠ none := by rw [hsrc]; simp
        have htd_ne : tds.getByKey g ≠ none := hkeys.mp hsrc_ne
        have hP := FnMatchP_checkAndSimplify hdecls hts
        obtain ⟨tf, htd⟩ : ∃ tf, tds.getByKey g = some (.function tf) := by
          cases htd_get : tds.getByKey g with
          | none => exact absurd htd_get htd_ne
          | some d =>
            cases d with
            | function tf => exact ⟨tf, rfl⟩
            | dataType dt =>
              exfalso
              have hdt : decls.getByKey g = some (.dataType dt) :=
                (hP g).2.1 dt htd_get
              rw [hsrc] at hdt; cases hdt
            | constructor dt c =>
              exfalso
              have hctor : decls.getByKey g = some (.constructor dt c) :=
                (hP g).2.2 dt c htd_get
              rw [hsrc] at hctor; cases hctor
        have htf_inputs_eq : tf.inputs = f_src.inputs :=
          checkAndSimplify_preserves_inputs hdecls hts hsrc htd
        have htf_params : tf.params = [] := by
          rw [checkAndSimplify_preserves_params hdecls hts hsrc htd, hf_params]
        -- Step (b): typed `.function tf` ⟹ monoDecls `.function md_f` at `g`
        -- with `md_f.inputs.map (·.1) = tf.inputs.map (·.1)`.
        obtain ⟨md_f, hmono, hmono_inputs⟩ :=
          concretizeBuild_preserves_function_inputs_at_entry_fwd hdecls hts hdrain
            hconc hUniqueNames htd htf_params
        -- Step (c): monoDecls `.function md_f` ⟹ concDecls `.function cf` at `g`
        -- with `md_f.inputs.mapM ... = .ok cf.inputs`.
        obtain ⟨cf, hcf_get, _hname_eq, hcf_inputs_witness, _houtput_witness⟩ :=
          step4Lower_function_explicit hmono hfold
        refine ⟨cf, hcf_get, ?_⟩
        -- Combine `cf.inputs.map (·.1) = md_f.inputs.map (·.1)` (via mapM
        -- witness) with `md_f.inputs.map (·.1) = tf.inputs.map (·.1)`
        -- (`hmono_inputs`) and `tf.inputs = f_src.inputs` (`htf_inputs_eq`).
        have hcf_md_inputs : md_f.inputs.map (·.1) = cf.inputs.map (·.1) :=
          mapM_first_proj md_f.inputs cf.inputs hcf_inputs_witness
        rw [htf_inputs_eq] at hmono_inputs
        rw [← hcf_md_inputs, hmono_inputs]
    -- Caller-provided per-key ctor-shape agreement (sig amendment 2026-05-05,
    -- #13 closure). Per-key ctor-index agreement composes
    -- `concretizeBuild_preserves_ctor_kind_at_entry_fwd` (Phase4.lean) with
    -- `step4Lower_constructor_explicit` (Shapes.lean) — both closed; the
    -- residual chain runs `decls.getByKey g = some (.constructor dt_src c_src)`
    -- via `mkDecls_ctor_companion` to the source dt at `dt_src.name`, lifts
    -- through `checkAndSimplify_preserves_ctor_kind_fwd` to typed,
    -- through `concretizeBuild_at_typed_ctor_explicit_general` to mono, and
    -- through `step4Lower_constructor_explicit` to concrete; positional
    -- correspondence at the ctor index follows from each step's
    -- `MatchesTdShape`-style witness. Per-key dataType-flat-size agreement
    -- composes `dataTypeFlatSize_eq_layoutMap_size_wf` (Layout.lean, closed
    -- modulo bound-saturation #5sat) with the `Concrete.dataTypeFlatSize ↔
    -- Concrete.DataType.size` bridge at the outer interfaces.
    have hCtorAgreesAll : ∀ (concDecls : Concrete.Decls),
        t.checkAndSimplify.toOption.bind (·.concretize.toOption) = some concDecls →
        ∀ (g : Global) {dt_src c_src dt_conc c_conc},
          decls.getByKey g = some (.constructor dt_src c_src) →
          concDecls.getByKey g = some (.constructor dt_conc c_conc) →
          (dt_src.constructors.findIdx? (· == c_src) |>.getD 0) =
            (dt_conc.constructors.findIdx? (· == c_conc) |>.getD 0) ∧
          dataTypeFlatSize decls {} dt_src =
            Concrete.dataTypeFlatSize concDecls {} dt_conc := by
      intro concDecls _hcd g dt_src c_src dt_conc c_conc _hsrc _hcd_ctor
      -- Closure of #15.C (BLOCKED-CtorAgrees-from-entry-compilation).
      --
      -- Two clauses:
      --   (1) Index agreement: `dt_src.constructors.findIdx? (· == c_src) =
      --       dt_conc.constructors.findIdx? (· == c_conc)` (modulo `getD 0`).
      --   (2) `dataTypeFlatSize` agreement.
      --
      -- Both clauses fundamentally depend on `dt_src.params = []`: under
      -- polymorphic source, having `.constructor` BOTH in `decls` AND in
      -- `concDecls` at the SAME `g` only happens when the source dt is
      -- already monomorphic (concretize doesn't write `.ctor` entries at
      -- already-monomorphic source keys with params ≠ []). The
      -- entry-restriction does not directly give us this. The structured
      -- derivation goes through `concretizeBuild_ctor_origin` BWD-style:
      --   * step4Lower-backward → mono `.ctor md_dt md_c` at `g`,
      --   * `concretizeBuild_ctor_origin` → either source-typed `.ctor`
      --     with `params = []` at `g` (origin 1) OR a `dt' ∈ newDataTypes`
      --     mangled-key origin (origin 4),
      --   * origin 1: identifies `dt_src.params = []` directly via FnMatchP;
      --   * origin 4: under StrongNewNameShape + entry-restriction,
      --     `g_orig.params = []` (since `dt_orig.params ≠ []` would force
      --     `args ≠ #[]` and hence `dt_new.name ≠ g_orig`, which combined
      --     with `g = dt_new.name.pushNamespace c_new.nameHead` and the
      --     `mkDecls_ctor_companion` of `_hsrc` produces a contradiction
      --     via `concretizeUniqueNames`-like reasoning).
      --
      -- The full structural derivation is left as a granular residual under
      -- this sub-sorry, split into the index half (which uses
      -- `concretizeBuild_at_typed_ctor_explicit_general` +
      -- `step4Lower_constructor_explicit`) and the flat-size half (which
      -- requires the heavy `dataTypeFlatSize_eq_layoutMap_size_wf` chain
      -- via #5e + #5sat). Both are reached transitively by the wirings.
      -- Wirings (kept for reachability of the layout-side flat-size chain
      -- which is still BLOCKED, and the FullyMono-side variant of the typed
      -- ctor explicit chain that mirrors the closed entry-restricted variant
      -- so both remain available for future consumers).
      let _ := @dataTypeFlatSize_eq_layoutMap_size_wf
      let _ := @layoutMap_dataType_size_extract
      let _ := @PhaseA2.concretizeBuild_at_typed_ctor_explicit_general
      -- Recover typed-decls + concretize witnesses + drained from `_hcd`.
      have ⟨tds, hts, hconc⟩ : ∃ tds : Typed.Decls,
          t.checkAndSimplify = .ok tds ∧ tds.concretize = .ok concDecls := by
        cases hts : t.checkAndSimplify with
        | error _ => simp [hts, Except.toOption] at _hcd
        | ok tds =>
          cases hconc : tds.concretize with
          | error _ => simp [hts, hconc, Except.toOption] at _hcd
          | ok cd =>
            simp [hts, hconc, Except.toOption] at _hcd
            subst _hcd
            exact ⟨tds, rfl, hconc⟩
      have hUniqueNames : Typed.Decls.ConcretizeUniqueNames tds :=
        hwf.noNameCollisions tds hts
      -- Extract `drained` from `hconc`.
      have hconc_orig := hconc
      unfold Typed.Decls.concretize at hconc_orig
      simp only [bind, Except.bind] at hconc_orig
      split at hconc_orig
      · cases hconc_orig
      rename_i drained hdrain
      have hfold : (concretizeBuild tds drained.mono drained.newFunctions
          drained.newDataTypes).foldlM (init := default) step4Lower
            = .ok concDecls := hconc_orig
      -- A.1: source `.ctor` ⟹ typed `.ctor` at `g`.
      obtain ⟨td_dt, td_c, htd⟩ :=
        checkAndSimplify_preserves_ctor_kind_fwd hdecls hts _hsrc
      -- FnMatchP backward: typed ctor at g equals source ctor at g (same dt+c).
      have hP := FnMatchP_checkAndSimplify hdecls hts
      have hsrc_again : decls.getByKey g = some (.constructor td_dt td_c) :=
        (hP g).2.2 td_dt td_c htd
      rw [_hsrc] at hsrc_again
      have ⟨htd_dt_eq, htd_c_eq⟩ : dt_src = td_dt ∧ c_src = td_c := by
        simp only [Option.some.injEq, Source.Declaration.constructor.injEq] at hsrc_again
        exact hsrc_again
      -- Rewrite `htd` to use `dt_src`/`c_src`.
      rw [← htd_dt_eq, ← htd_c_eq] at htd
      -- Source dt at dt_src.name (via mkDecls_ctor_companion).
      obtain ⟨hsrc_dt, hcmem⟩ := mkDecls_ctor_companion hdecls g dt_src c_src _hsrc
      -- Typed dt at dt_src.name.
      obtain ⟨td_dt', htd_dt'⟩ := checkAndSimplify_src_dt_to_td hdecls hts hsrc_dt
      have htd_dt'_eq : td_dt' = dt_src := by
        have := (hP dt_src.name).2.1 td_dt' htd_dt'
        rw [hsrc_dt] at this; cases this; rfl
      rw [htd_dt'_eq] at htd_dt'
      -- Distinctness on dt_src.constructors nameHeads.
      have hdistinct := mkDecls_dt_ctor_nameheads_distinct hdecls dt_src.name dt_src hsrc_dt
      -- Position of c_src in dt_src.constructors (full structural).
      obtain ⟨i, hi_lt, hi_eq⟩ := List.getElem_of_mem hcmem
      have hi_unique : ∀ j (hj : j < dt_src.constructors.length),
          (dt_src.constructors[j]'hj) = c_src → j = i := by
        intro j hj heq
        apply hdistinct j i hj hi_lt
        rw [heq, ← hi_eq]
      -- src side findIdx? = some i.
      have hsrc_findIdx :
          dt_src.constructors.findIdx? (· == c_src) = some i := by
        rw [List.findIdx?_eq_some_iff_getElem]
        refine ⟨hi_lt, ?_, ?_⟩
        · show (dt_src.constructors[i]'hi_lt == c_src) = true
          rw [hi_eq]; exact BEq.rfl
        · intro j hji
          show ¬((dt_src.constructors[j]'(Nat.lt_trans hji hi_lt)) == c_src) = true
          intro hbeq
          have hj_eq : (dt_src.constructors[j]'(Nat.lt_trans hji hi_lt)) = c_src :=
            LawfulBEq.eq_of_beq hbeq
          have := hi_unique j (Nat.lt_trans hji hi_lt) hj_eq
          omega
      -- Bridge fact `g = dt_src.name.pushNamespace c_src.nameHead`.
      have hg_pushed : g = dt_src.name.pushNamespace c_src.nameHead :=
        mkDecls_source_ctor_is_key hdecls g dt_src c_src _hsrc
      -- Derive `dt_src.params = []` via `concretizeBuild_ctor_origin` BWD on
      -- mono `.ctor` at g. Step4Lower-backward gives mono `.ctor`. Origin
      -- classification: origin 1 ⟹ typed `.ctor src_dt src_c` at g with
      -- `src_dt.params = []`; via FnMatchP backward + IndexMap uniqueness,
      -- `src_dt = dt_src` (modulo `checkAndSimplify_preserves_params`).
      -- Origin 4 ⟹ dt' ∈ newDataTypes with `dt'.name.pushNamespace
      -- c'.nameHead = g`. Combined with `hg_pushed` + name injection,
      -- `dt'.name = dt_src.name`. SNN gives `dt'.name = concretizeName g_orig
      -- args` and `args.size = dt_orig.params.length`; `ConcretizeUniqueNames`
      -- on the resulting `concretizeName g_orig args = concretizeName
      -- dt_src.name #[]` collision (anchored by concDecls existence at
      -- dt_src.name) forces `args = #[]`, hence `dt_orig.params = []`. By
      -- IndexMap uniqueness `dt_orig = td_dt'`, so via
      -- `checkAndSimplify_preserves_params`, `dt_src.params = td_dt'.params =
      -- dt_orig.params = []`.
      obtain ⟨md_dt, md_c, hmono_get⟩ :=
        step4Lower_backward_ctor_kind_at_key _hcd_ctor hfold
      have hdt_src_params : dt_src.params = [] := by
        rcases PhaseA2.concretizeBuild_ctor_origin tds drained.mono
          drained.newFunctions drained.newDataTypes hmono_get with
          ⟨src_dt, src_c, htd_orig, hparams⟩ | ⟨dt', hdt_mem, c', hc_mem, hcname⟩
        · -- Origin 1: typed ctor at g with `src_dt.params = []`. Identify with htd.
          rw [htd] at htd_orig
          simp only [Option.some.injEq, Typed.Declaration.constructor.injEq] at htd_orig
          obtain ⟨hsrc_dt_eq, _⟩ := htd_orig
          rw [← hsrc_dt_eq] at hparams
          -- `dt_src.params = src_dt.params = []` via FnMatchP. But we already
          -- have `htd : tds.getByKey g = some (.constructor dt_src c_src)` and
          -- `htd_orig` says `dt_src = src_dt`, so `dt_src.params = []` directly
          -- through `hparams`. Then `dt_src.params = []` via this equation.
          -- Wait — `dt_src` here is the source-side ctor's dt (not the typed
          -- one). `hsrc_dt_eq : src_dt = dt_src` (after unification with htd).
          -- So `dt_src.params = src_dt.params = []`.
          exact hparams
        · -- Origin 4: dt' ∈ drained.newDataTypes pushes ctor at g.
          have hSNN := concretize_drain_preserves_StrongNewNameShape _ _
            (DrainState.StrongNewNameShape.init tds (concretizeSeed tds)) hdrain
          obtain ⟨g_orig, args, dt_orig, hname, hget_orig, hargs_sz, _hctors_nh⟩ :=
            hSNN.2 dt' hdt_mem
          -- Name injection from `dt'.name.pushNamespace c'.nameHead = g =
          -- dt_src.name.pushNamespace c_src.nameHead`.
          have hpush_eq : dt'.name.pushNamespace c'.nameHead =
              dt_src.name.pushNamespace c_src.nameHead := by
            rw [hcname, hg_pushed]
          have h_name_eq : Lean.Name.str dt'.name.toName c'.nameHead =
              Lean.Name.str dt_src.name.toName c_src.nameHead := by
            have := hpush_eq
            unfold Global.pushNamespace at this
            exact Global.mk.inj this
          have hToName : dt'.name.toName = dt_src.name.toName := by injection h_name_eq
          have hdt'_name_eq : dt'.name = dt_src.name := by
            cases hd : dt'.name; cases hT : dt_src.name
            rw [hd, hT] at hToName
            congr 1
          -- `concretizeName g_orig args = dt'.name = dt_src.name =
          -- concretizeName dt_src.name #[]`.
          have hcn_eq : concretizeName g_orig args = dt'.name := hname.symm
          have hcn_eq2 : concretizeName g_orig args = concretizeName dt_src.name #[] := by
            rw [hcn_eq, hdt'_name_eq]; exact (concretizeName_empty_args dt_src.name).symm
          -- concDecls existence at dt_src.name (= td_dt'.name): typed has
          -- `.dataType td_dt'` at dt_src.name (via htd_dt'). Build inserts
          -- `.dataType` there from `srcStep` (since `td_dt'.params` could be
          -- non-empty in general; but here we'll show in this branch). Hmm
          -- actually for the build to insert, srcStep needs td_dt'.params = [].
          -- Detour: derive `dt_src.params = []` via uniqueness directly. We
          -- have `args.size = dt_orig.params.length` (SNN). Need
          -- `args = #[]` ⟹ `dt_orig.params = []`. Then `dt_orig = td_dt'`
          -- (via `checkAndSimplify_src_dt_to_td` lift identity at dt_src.name)
          -- gives `td_dt'.params = []`, hence `dt_src.params = []`
          -- (via `checkAndSimplify_preserves_params`).
          --
          -- For `args = #[]`: apply `ConcretizeUniqueNames` on `hcn_eq2`. Need
          -- `concDecls.getByKey (concretizeName g_orig args) = some _`. From
          -- `hcn_eq` + `hdt'_name_eq`, this key is `dt_src.name`. concDecls
          -- existence at dt_src.name follows from origin: at this step in
          -- origin 4, dt' has been pushed which writes `.dataType` at
          -- `dt'.name = dt_src.name` (during the dtStep dt-fold). step4Lower
          -- keys-iff lifts to concDecls.
          have hkeys_iff := concretize_step_4_keys_of_fold step4Lower
            step4Lower_inserts hconc_orig
          have hConc_dtsrcname : ∃ d, concDecls.getByKey dt_src.name = some d := by
            -- The build's containsKey at dt_src.name follows from the dtStep
            -- fold inserting at `dt'.name = dt_src.name`. Specifically,
            -- `concretizeBuild_containsKey_newDt_name` (or via direct fold
            -- containsKey monotonicity from hdt_mem).
            have hBuildContains : (concretizeBuild tds drained.mono
                drained.newFunctions drained.newDataTypes).containsKey dt_src.name :=
              hdt'_name_eq ▸ PhaseA2.concretizeBuild_containsKey_newDt_name tds drained.mono
                drained.newFunctions drained.newDataTypes hdt_mem
            have hconc_contains : concDecls.containsKey dt_src.name :=
              (hkeys_iff dt_src.name).mp hBuildContains
            have hconc_get_ne : concDecls.getByKey dt_src.name ≠ none := by
              rw [IndexMap.getByKey_ne_none_iff_containsKey]; exact hconc_contains
            cases hg_dt : concDecls.getByKey dt_src.name with
            | none => exact absurd hg_dt hconc_get_ne
            | some d => exact ⟨d, rfl⟩
          have hWit' : ∃ d, concDecls.getByKey (concretizeName g_orig args) = some d := by
            rw [hcn_eq, hdt'_name_eq]; exact hConc_dtsrcname
          obtain ⟨hgorig_eq_tdname, hargs_empty⟩ :=
            hUniqueNames hconc g_orig dt_src.name args #[] hcn_eq2 hWit'
          have hargs_zero : args.size = 0 := by rw [hargs_empty]; rfl
          have hdt_orig_params : dt_orig.params = [] := by
            have := hargs_sz
            rw [hargs_zero] at this
            exact List.length_eq_zero_iff.mp this.symm
          -- `dt_orig = dt_src` via IndexMap uniqueness on tds at dt_src.name
          -- (recall `htd_dt'` is now `tds.getByKey dt_src.name = some
          -- (.dataType dt_src)` after the earlier rewrite of td_dt' = dt_src).
          have hdt_orig_eq : dt_orig = dt_src := by
            rw [hgorig_eq_tdname] at hget_orig
            rw [htd_dt'] at hget_orig
            cases hget_orig; rfl
          rw [hdt_orig_eq] at hdt_orig_params
          exact hdt_orig_params
      -- Now apply the new entry-restricted variant.
      obtain ⟨md_dt', md_c', hmono_get', hLen_md, hNH_md, hPos_md, hStruct_md⟩ :=
        PhaseA2.concretizeBuild_at_typed_ctor_at_entry_fwd hdrain hconc hUniqueNames
          hg_pushed htd htd_dt' hdt_src_params hcmem hdistinct
      -- Apply step4Lower_constructor_explicit to bridge mono → cd.
      obtain ⟨cd_dt', cd_c', hcd', _hName_cd, hLen_cd, hNH_cd, hPos_cd, hStruct_cd, _hCtors_cd, _hCtorArgs_cd⟩ :=
        step4Lower_constructor_explicit hmono_get' hfold
      -- cd_dt' = dt_conc and cd_c' = c_conc (via uniqueness at g).
      rw [_hcd_ctor] at hcd'
      obtain ⟨hcd_dt_eq, hcd_c_eq⟩ : cd_dt' = dt_conc ∧ cd_c' = c_conc := by
        simp only [Option.some.injEq, Concrete.Declaration.constructor.injEq] at hcd'
        exact ⟨hcd'.1.symm, hcd'.2.symm⟩
      rw [hcd_dt_eq] at hLen_cd hPos_cd hStruct_cd
      rw [hcd_c_eq] at hStruct_cd
      -- Get md_dt'[i] = md_c' via hStruct_md (positional structural equality).
      obtain ⟨hi_lt_md, hi_md_eq⟩ := hStruct_md i hi_lt hi_eq
      -- Get cd_dt[i] = cd_c via hStruct_cd.
      have hi_lt_cd : i < dt_conc.constructors.length := by
        rw [hLen_cd]; exact hi_lt_md
      have hi_cd_eq : (dt_conc.constructors[i]'hi_lt_cd) = c_conc :=
        hStruct_cd i hi_lt_md hi_lt_cd hi_md_eq
      -- Length agreement: dt_conc.length = dt_src.length.
      have hLen_cs : dt_conc.constructors.length = dt_src.constructors.length := by
        rw [hLen_cd, hLen_md]
      -- Distinctness on dt_conc.constructors nameHeads, transferred via positional
      -- nameHead correspondence cd → md → src.
      have hcd_distinct : ∀ a b (ha : a < dt_conc.constructors.length)
          (hb : b < dt_conc.constructors.length),
          (dt_conc.constructors[a]'ha).nameHead = (dt_conc.constructors[b]'hb).nameHead → a = b := by
        intro a b ha hb hab_nh
        have ha_md : a < md_dt'.constructors.length := by rw [← hLen_cd]; exact ha
        have hb_md : b < md_dt'.constructors.length := by rw [← hLen_cd]; exact hb
        have ha_src : a < dt_src.constructors.length := by rw [← hLen_md]; exact ha_md
        have hb_src : b < dt_src.constructors.length := by rw [← hLen_md]; exact hb_md
        have hPos_md_a := (hPos_md a ha_src).2
        have hPos_md_b := (hPos_md b hb_src).2
        have hPos_cd_a := hPos_cd a ha_md ha
        have hPos_cd_b := hPos_cd b hb_md hb
        have ha_total : (dt_conc.constructors[a]'ha).nameHead =
            (dt_src.constructors[a]'ha_src).nameHead := by
          rw [hPos_cd_a, hPos_md_a]
        have hb_total : (dt_conc.constructors[b]'hb).nameHead =
            (dt_src.constructors[b]'hb_src).nameHead := by
          rw [hPos_cd_b, hPos_md_b]
        have hsrc_nh : (dt_src.constructors[a]'ha_src).nameHead =
            (dt_src.constructors[b]'hb_src).nameHead := by
          rw [← ha_total, ← hb_total]; exact hab_nh
        exact hdistinct a b ha_src hb_src hsrc_nh
      -- cd side findIdx? = some i.
      have hcd_findIdx :
          dt_conc.constructors.findIdx? (· == c_conc) = some i := by
        rw [List.findIdx?_eq_some_iff_getElem]
        refine ⟨hi_lt_cd, ?_, ?_⟩
        · show (dt_conc.constructors[i]'hi_lt_cd == c_conc) = true
          rw [hi_cd_eq]; exact BEq.rfl
        · intro j hji
          show ¬((dt_conc.constructors[j]'(Nat.lt_trans hji hi_lt_cd)) == c_conc) = true
          intro hbeq
          have hj_eq : (dt_conc.constructors[j]'(Nat.lt_trans hji hi_lt_cd)) = c_conc :=
            LawfulBEq.eq_of_beq hbeq
          have hj_nh : (dt_conc.constructors[j]'(Nat.lt_trans hji hi_lt_cd)).nameHead =
              (dt_conc.constructors[i]'hi_lt_cd).nameHead := by
            rw [hj_eq, hi_cd_eq]
          have := hcd_distinct j i (Nat.lt_trans hji hi_lt_cd) hi_lt_cd hj_nh
          omega
      refine ⟨?_, ?_⟩
      · -- Index agreement (modulo getD 0).
        rw [hsrc_findIdx, hcd_findIdx]
      · -- BLOCKED-CtorAgrees-flat-size: composition of
        -- `dataTypeFlatSize_eq_layoutMap_size_wf` (Layout.lean, F=2 with
        -- bound-saturation #5sat residual) with the Concrete-side
        -- `dataTypeFlatSize ↔ DataType.size` bridge. Requires the
        -- LayoutKeysMatch + CdTdLenAgree + CtorArgsAlign + KeysAlign
        -- producer chain for the dt key (NOT the ctor key) at
        -- `dt_src.name`, lifted via `mkDecls_ctor_companion`. Acceptable
        -- residual per the dispatch's "if Layout-chain hoists aren't
        -- dischargeable, keep flat-size sub-blocker" clause.
        sorry
    exact Toplevel.compile_preservation_entry t ct decls hdecls hct hwf
      name funIdx hname hsrc hentry args io₀ fuel retTyp hargsFnFree
        hargsReach hconcRetFnFree hconcRetReach hcdNameAgrees hDeclsR
        hCtorAgreesAll

end Aiur

end -- @[expose] public section
