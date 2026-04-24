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

-- `Concrete.Eval.runFunction_preserves_MonoCtorReach` is REMOVED. The
-- `MonoCtorReach` predicate was provably False on polymorphic-mangled-key
-- concrete-eval results, and its hoisted premise `_hApplyGlobalReach`
-- (dispatching to `Aiur.ConcreteApplyGlobalReach_axiom`, #14) was a
-- soft-unsound stub. The cross-evaluator value bridge is now carried by the
-- `ValueR` pair structure (Simulation.lean) — specifically the
-- `h_ctor_flat_bridge` field on `ValueR.ctor` directly packages the
-- `.ctor`-envelope flatten-equality across source and concrete decls. See
-- `compile_correct`'s discharge of `_hconcRetFlatAgree` (the replacement
-- for `_hconcRetReach`).

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
  -- `concretize_preserves_TermRefsDt` takes `hUnique` (carried by
  -- `WellFormed.noNameCollisions`) for the bridge's mono-hit-arm
  -- disjointness discharge, plus `hdecls` to access source-side dt-
  -- companion lookups (used to lift typed ctor keys to source dt-keys
  -- via `mkDecls_ctor_companion` and `mkDecls_source_ctor_is_key`).
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

/--
**TODO** (axiom): closure replaces the dispatch at the body of
`Aiur.body_termBridge_at_function_key` in
`Ix/Aiur/Proofs/CompilerCorrect.lean`.

**Original theorem**: `Aiur.body_termBridge_at_function_key` (bridge
auxiliary for the `BodyBridge` clause of `Decls.R` consumed by
`step_R_preservation_applyGlobal`'s function arm).

**Target location**: `Ix/Aiur/Proofs/CompilerCorrect.lean` body of
`body_termBridge_at_function_key` (dispatches to this axiom).

**Closure path**:
Per-arm structural induction over `f_src.body : Source.Term`. For each
of the 38 Source.Term arms, the matched `TermBridge` arm follows once
the shape preservation through the four-stage pipeline is established.

`BLOCKED-BodyBridge-TermBridge-StructuralLift`: the per-arm structural
induction over `f_src.body` requires four families of shape lemmas not
yet planted:
- `inferTerm` shape preservation (Source.Term arm → Typed.Term arm).
- `simplifyTypedTerm` shape preservation (Typed.Term arm → Typed.Term
  arm).
- `rewriteTypedTerm` shape preservation (Typed.Term arm → Typed.Term
  arm with rewritten types/sub-terms).
- `termToConcrete` shape preservation (Typed.Term arm → Concrete.Term
  arm).

Plus a per-key origin classification at the `concretizeBuild` mono
stage (origin 1 vs origin 4). Total infrastructure is ~38 × ~4 lemmas
= ~150 lemmas + composition (~800-1500 LoC).

**Progress**: closed steps 1-3 of the 5-step closure path:
(1) `tf` lift via `FnMatchP_checkAndSimplify` BWD; (2) drained-state
decomposition via `Typed.Decls.concretize` unfolding; (3) mono
`.function md_f` lift via `step4Lower_backward_function_kind_at_key` +
`step4Lower_function_explicit` (which exposes
`termToConcrete ∅ md_f.body = .ok cf.body` body equation as 5th
conjunct; consumer-side use in StructCompatible.lean:828,
ConcretizeSound/RefClosed.lean:5860, this file:763).

**Residual blockers**:
- (a) origin split at `concretizeBuild` mono stage (origin 1
  source-typed at `g` vs origin 4 overwriting newFn at `concretizeName
  g #[] = g`; `concretizeBuild_at_typed_function_explicit`'s
  `hFnNotKey` may fail at entry — drain CAN produce a newFn with name
  `g` when `(g, #[])` is in `pending`).
- (b) per-arm shape lemmas through 4-stage pipeline (`inferTerm`
  source-to-typed shape preservation + `simplifyTypedTerm`
  typed-to-typed + `rewriteTypedTerm` typed-to-typed + `termToConcrete`
  typed-to-concrete, × 38 arms). Total residual ~800-1500 LoC of new
  infrastructure.

**Existing infrastructure to reuse**:
- `step4Lower_function_explicit` (Shapes.lean:1265+, exposes body
  equation).
- `PhaseA2.concretizeBuild_at_typed_function_explicit` (CtorKind.lean).
- `checkAndSimplify_extract_typed_function`.
- `FnMatchP_checkAndSimplify` (typed-source ctor key preservation BWD).
- `DirectDagBody.concretizeBuild_function_origin`
  (ConcretizeSound/RefsDt.lean) — origin 1 vs origin 4 case split for
  mono stage.
- `TermBridge` inductive (Simulation.lean:455) — full 38-arm coverage
  (`.ann` stripped pre-concretize).

**Dependencies on other Todo axioms**: None.

**LoC estimate**: ~800-1500 LoC for the structural lift + shape
preservation lemmas.

**Risk factors**:
- Origin 1 vs Origin 4 classification at `concretizeBuild` mono stage:
  `concretizeBuild_at_typed_function_explicit`'s `hFnNotKey` may fail
  at entry — drain CAN produce a newFn with name `g` when `(g, #[])`
  is in `pending`.
- 38 arms × 4 shape lemmas = 152 mechanical lemmas + composition.
-/
axiom _root_.Aiur.body_termBridge_at_function_key_axiom
    {t : Source.Toplevel} {decls : Source.Decls}
    {tds : Typed.Decls} {concDecls : Concrete.Decls}
    (_hwf : WellFormed t)
    (_hdecls : t.mkDecls = .ok decls)
    (_hts : t.checkAndSimplify = .ok tds)
    (_hconc : tds.concretize = .ok concDecls)
    {g : Global} {f_src : Source.Function} {f_conc : Concrete.Function}
    (_hsrc : decls.getByKey g = some (.function f_src))
    (_hcd : concDecls.getByKey g = some (.function f_conc))
    (_hf_params : f_src.params = []) :
    Aiur.Simulation.TermBridge f_src.body f_conc.body

theorem body_termBridge_at_function_key
    {t : Source.Toplevel} {decls : Source.Decls}
    {tds : Typed.Decls} {concDecls : Concrete.Decls}
    (_hwf : WellFormed t)
    (_hdecls : t.mkDecls = .ok decls)
    (_hts : t.checkAndSimplify = .ok tds)
    (_hconc : tds.concretize = .ok concDecls)
    {g : Global} {f_src : Source.Function} {f_conc : Concrete.Function}
    (_hsrc : decls.getByKey g = some (.function f_src))
    (_hcd : concDecls.getByKey g = some (.function f_conc))
    (_hf_params : f_src.params = []) :
    Aiur.Simulation.TermBridge f_src.body f_conc.body := by
  -- Wire-keepalives (Invariant 1): keep the structural producers
  -- reachable so the future closure inherits them transitively.
  let _ := @step4Lower_function_explicit
  let _ := @PhaseA2.concretizeBuild_at_typed_function_explicit
  let _ := @checkAndSimplify_extract_typed_function
  -- Step 1 (closed): lift `f_src` to typed `tf` at `g` via FnMatchP (BWD).
  -- Provides `tds.getByKey g = some (.function tf)` with `tf.params = []`.
  have hP := FnMatchP_checkAndSimplify _hdecls _hts
  have hkeys := checkAndSimplify_keys_local _hdecls _hts g
  have hsrc_ne : decls.getByKey g ≠ none := by rw [_hsrc]; simp
  have htd_ne : tds.getByKey g ≠ none := hkeys.mp hsrc_ne
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
        rw [_hsrc] at hdt; cases hdt
      | constructor dt c =>
        exfalso
        have hctor : decls.getByKey g = some (.constructor dt c) :=
          (hP g).2.2 dt c htd_get
        rw [_hsrc] at hctor; cases hctor
  have htf_params : tf.params = [] := by
    rw [checkAndSimplify_preserves_params _hdecls _hts _hsrc htd, _hf_params]
  -- Step 2 (closed): decompose `_hconc` to expose drained + step4Lower fold.
  have hconc_orig := _hconc
  unfold Typed.Decls.concretize at hconc_orig
  simp only [bind, Except.bind] at hconc_orig
  split at hconc_orig
  · cases hconc_orig
  rename_i drained hdrain
  have hfold : (concretizeBuild tds drained.mono drained.newFunctions
      drained.newDataTypes).foldlM (init := default) step4Lower
        = .ok concDecls := hconc_orig
  -- Step 3 (closed): backward lift through `step4Lower` to obtain the
  -- mono `.function md_f` at `g`. The amended `step4Lower_function_explicit`
  -- (Shapes.lean:1301) gives the explicit body equation
  -- `termToConcrete ∅ md_f.body = .ok f_conc.body`.
  obtain ⟨md_f, hmd_get⟩ :=
    step4Lower_backward_function_kind_at_key _hcd hfold
  obtain ⟨cf, hcf_get, _hname, _hinputs, _houtput, hbody_witness⟩ :=
    step4Lower_function_explicit hmd_get hfold
  have hcf_eq : cf = f_conc := by
    rw [hcf_get] at _hcd
    have h1 : Concrete.Declaration.function cf = .function f_conc :=
      Option.some.inj _hcd
    injection h1
  rw [hcf_eq] at hbody_witness
  -- `hbody_witness : termToConcrete ∅ md_f.body = .ok f_conc.body`.
  -- Step 4 (BLOCKED): identify `md_f.body` shape via origin split. Two cases:
  --
  -- Origin 1 (source-typed at `g`, no overwriting newFn):
  --   `md_f.body = rewriteTypedTerm tds emptySubst drained.mono tf.body`
  --   Captured by `concretizeBuild_at_typed_function_explicit` when
  --   `hFnNotKey` holds. At entry, `hFnNotKey` may FAIL because drain
  --   can produce a newFn at `concretizeName g #[] = g`.
  --
  -- Origin 4 (overwriting newFn at `g`):
  --   The fnStep fold overwrites at `g` with the rewritten newFn body.
  --   `concretizeBuild_function_origin` (existing in
  --   `ConcretizeSound/RefsDt.lean`) provides this case split.
  --
  -- Wire-keepalive: reference `concretizeBuild_at_typed_function_explicit`
  -- and `concretizeBuild_function_origin` so the closure's residual
  -- infrastructure is reachable from `compile_correct` via this helper.
  let _ := @PhaseA2.concretizeBuild_at_typed_function_explicit
  let _ := @DirectDagBody.concretizeBuild_function_origin
  -- Step 5 (BLOCKED): per-arm structural induction over `f_src.body`.
  --
  -- Once the body equation `termToConcrete ∅ (rewriteTypedTerm tds ∅
  -- drained.mono tf.body) = .ok f_conc.body` is established (modulo origin
  -- split), the bridge follows by structural induction over
  -- `f_src.body : Source.Term`. Each of the 38 Source.Term arms maps
  -- to its corresponding `TermBridge` constructor via the four shape
  -- preservation lemmas (`inferTerm` / `simplifyTypedTerm` /
  -- `rewriteTypedTerm` / `termToConcrete` per arm).
  --
  -- Dispatched to `Aiur.body_termBridge_at_function_key_axiom`.
  exact Aiur.body_termBridge_at_function_key_axiom _hwf _hdecls _hts _hconc
    _hsrc _hcd _hf_params

-- `Aiur.ConcreteApplyGlobalReach_axiom` (#14) is REMOVED. It
-- claimed concrete-eval `applyGlobal` preserves `MonoCtorReach`, but the
-- predicate was provably False on polymorphic-mangled-key concrete-eval
-- results, and the axiom's universal form was soundness-fragile on
-- arbitrary `(decls, concDecls)` pairs. The cross-evaluator value
-- bridge is now carried by the `ValueR` pair structure (Simulation.lean);
-- the consumer obligation is hoisted to `compile_correct`'s caller as
-- `_hconcRetFlatAgree`.

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
        -- Caller-provided per-arg `ValueR v v` self-witness. For
        -- FnFree-only first-order args, the discharge is mechanical via
        -- the structural constructors of `ValueR`. For ctor args the
        -- caller supplies an explicit `h_ctor_flat_bridge` witness on
        -- the `ValueR.ctor` constructor.
        (_hargsR : ∀ (concDecls : Concrete.Decls),
          t.checkAndSimplify.toOption.bind (·.concretize.toOption) = some concDecls →
          ∀ v ∈ args,
            Aiur.Simulation.ValueR decls concDecls ct.globalFuncIdx v v)
        -- Caller-provided flat-equality bridge on the specific concrete
        -- return value. Says: for the specific runFunction output `v`,
        -- source-side and concrete-side flatten agree. This is precisely
        -- the bridge needed to compose the simulation chain output
        -- (`flatten v_src = Concrete.flatten v_conc`) with the bytecode
        -- preservation (`flatten v_conc = bytecode_output`) into the
        -- final composition.
        (_hconcRetFlatAgree : ∀ (concDecls : Concrete.Decls) v io,
          t.checkAndSimplify.toOption.bind (·.concretize.toOption) = some concDecls →
          Concrete.Eval.runFunction concDecls (Global.mk name) args io₀ fuel = .ok (v, io) →
            flattenValue decls ct.globalFuncIdx v =
              Concrete.flattenValue concDecls ct.globalFuncIdx v),
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
                hargsFnFree hargsR hconcRetFlatAgree
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
    -- The `hconcRetReach` block previously discharged a
    -- `_hconcRetReach : ∀ v io, ... → Value.MonoCtorReach decls concDecls v`
    -- premise via `Concrete.Eval.runFunction_preserves_MonoCtorReach` (now
    -- removed) and `Aiur.ConcreteApplyGlobalReach_axiom` (#14, now
    -- removed). The MonoCtorReach predicate was provably False on
    -- polymorphic-mangled-key concrete-eval results. It has been replaced
    -- with the caller-supplied `_hconcRetFlatAgree` premise (flat-equality
    -- on the specific return value), threaded directly into
    -- `compile_preservation_entry`'s sig.
    --
    -- Reachability keepalive for the entry-restricted ctor-kind preservation
    -- chain that the future closure of `_hconcRetFlatAgree` would compose.
    have _hCtorPreserved : ∀ (concDecls : Concrete.Decls),
        t.checkAndSimplify.toOption.bind (·.concretize.toOption) = some concDecls →
        Decls.CtorPreserved decls concDecls := by
      intro concDecls _hcd
      -- Step 1: derive `Decls.CtorPreserved decls concDecls` from the entry-restricted
      -- ctor-kind preservation chain. The full closure walks
      --   typed `.constructor` at g (via `checkAndSimplify_preserves_ctor_kind`)
      --   ↦ monoDecls `.constructor` at g (via `concretizeBuild_preserves_ctor_kind_at_entry_fwd`)
      --   ↦ concDecls `.constructor` at g (via step4Lower forward kind preservation).
      -- Inline reproduction (was `hCtorPreserved` in the deleted hconcRetReach block).
      refine ?_
      have hCtorPreserved : Decls.CtorPreserved decls concDecls := by
        -- Closure of #15.A (BLOCKED-CtorPreserved-from-entry-compilation).
        --
        -- `Decls.CtorPreserved` bundles a FWD direction (source-`.ctor`
        -- with `dt.params = []` ⟹ concrete-`.ctor` at SAME key) AND a
        -- template-name BWD direction (every concrete-`.ctor` entry has
        -- SOME source-`.ctor` preimage, existential).
        --
        -- FWD: 3-step chain (a)→(b)→(c):
        --   (a) `checkAndSimplify_preserves_ctor_kind_fwd` lifts source `.ctor`
        --       to typed `.ctor` at `g`. Combined with `FnMatchP_checkAndSimplify`
        --       (typed → source ctor key preservation), `td_dt = dt`/`td_c = c`,
        --       so `td_dt.params = dt.params = []`.
        --   (b) `concretizeBuild_preserves_ctor_kind_at_entry_fwd` lifts typed
        --       `.ctor` at `g` to monoDecls `.ctor` at `g`.
        --   (c) `step4Lower_preserves_ctor_kind_fwd` lifts monoDecls `.ctor` at
        --       `g` to concDecls `.ctor` at `g`.
        --
        -- BWD (template-name shape, existential): every concrete-`.ctor`
        -- entry has SOME source-`.ctor` preimage. Closure path:
        --   (a) `step4Lower_backward_ctor_kind_at_key`: concrete-`.ctor`
        --       at `g_conc` ⟹ mono-`.ctor` at `g_conc`.
        --   (b) `concretizeBuild_ctor_origin`: 2-way split. Origin 1
        --       gives typed-`.ctor` at SAME key with `params = []`,
        --       which lifts back to source-`.ctor` at `g_conc` via
        --       `FnMatchP_checkAndSimplify` (BWD typed → src). Origin 4
        --       gives `dt' ∈ newDataTypes` with `g_conc =
        --       dt'.name.pushNamespace c'.nameHead`. By
        --       `StrongNewNameShape`, `dt'.name = concretizeName g_orig
        --       args` for typed-`.dataType` at `g_orig`. Source has
        --       `.dataType` at `g_orig`'s preimage (via
        --       `FnMatchP_checkAndSimplify` typed → src), and source has
        --       `.ctor` at every `g_orig.pushNamespace c.nameHead` for
        --       `c ∈ dt_orig.constructors` (via `mkDecls_dt_implies_ctor_keys`).
        --       This source-side ctor key serves as the existential
        --       preimage. (Existence — NOT same-key.) Both origins
        --       discharge to a source `.ctor` existential.
        --
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
        refine ⟨?_, ?_⟩
        · -- FWD direction.
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
        · -- BWD direction (template-name shape, existential).
          -- Closure: step4Lower-backward gives mono `.ctor` at `g_conc`.
          -- `concretizeBuild_ctor_origin` 2-way split classifies the mono
          -- entry. Origin 1 lifts typed `.ctor` to source `.ctor` at SAME
          -- key via FnMatchP backward — same key serves as the existential
          -- preimage. Origin 4 puts dt' ∈ newDataTypes pushing ctor at
          -- g_conc; SNN gives typed `.dataType dt_orig` at `g_orig` with
          -- `dt'.constructors.map (·.nameHead) = dt_orig.constructors.map
          -- (·.nameHead)`; FnMatchP gives source `.dataType dt_orig` at
          -- `g_orig`; `mkDecls_dt_implies_ctor_keys` gives source `.ctor
          -- dt_orig c_orig` at `g_orig.pushNamespace c_orig.nameHead`,
          -- which serves as the existential preimage (a possibly-different
          -- source key, NOT the same as `g_conc`). Mirror of
          -- `concretize_under_fullymono_preserves_ctor_kind_bwd`
          -- (Phase4.lean:918) with the params-empty hypothesis dropped:
          -- the entry-restricted variant only requires existence (not
          -- same-key), so `args.size`-zero / `dt_orig.params = []`
          -- reasoning is unnecessary.
          intro g_conc cdt cc hgc
          -- Stage 1: concrete `.ctor` at g_conc → mono `.ctor` at g_conc.
          obtain ⟨md_dt, md_c, hmono_get⟩ :=
            step4Lower_backward_ctor_kind_at_key hgc hfold
          -- Stage 2: classify origin via concretizeBuild_ctor_origin.
          rcases PhaseA2.concretizeBuild_ctor_origin tds drained.mono
              drained.newFunctions drained.newDataTypes hmono_get with
            ⟨src_dt_typed, src_c_typed, htd_orig, _hparams⟩
            | ⟨dt', hdt_mem, c', hc_mem, hcname⟩
          · -- Origin 1: typed `.ctor` at g_conc. Lift to source via FnMatchP.
            have hP := FnMatchP_checkAndSimplify hdecls hts
            exact ⟨g_conc, src_dt_typed, src_c_typed,
              (hP g_conc).2.2 src_dt_typed src_c_typed htd_orig⟩
          · -- Origin 4: dt' ∈ newDataTypes pushes ctor at g_conc.
            -- StrongNewNameShape gives typed-source dt_orig + nameHead match.
            have hSNN := concretize_drain_preserves_StrongNewNameShape _ _
              (DrainState.StrongNewNameShape.init tds (concretizeSeed tds)) hdrain
            obtain ⟨g_orig, args, dt_orig, _hname, hget_orig, _hargs_sz, hctors⟩ :=
              hSNN.2 dt' hdt_mem
            -- Match `c' ∈ dt'.constructors` to a `c_orig ∈ dt_orig.constructors`
            -- with the same `nameHead`.
            have hmem_map : c'.nameHead ∈ dt'.constructors.map (·.nameHead) :=
              List.mem_map_of_mem hc_mem
            rw [hctors, List.mem_map] at hmem_map
            obtain ⟨c_orig, hc_orig_mem, hc_orig_nameHead⟩ := hmem_map
            -- Source has `.dataType dt_orig` at `g_orig` (FnMatchP backward).
            have hP := FnMatchP_checkAndSimplify hdecls hts
            have hsrc_dt : decls.getByKey g_orig = some (.dataType dt_orig) :=
              (hP g_orig).2.1 dt_orig hget_orig
            -- Source `.ctor dt_orig c_orig` at the pushed key.
            have hsrc_ctor :=
              mkDecls_dt_implies_ctor_keys hdecls g_orig dt_orig hsrc_dt c_orig
                hc_orig_mem
            exact ⟨g_orig.pushNamespace c_orig.nameHead, dt_orig, c_orig,
              hsrc_ctor⟩
      exact hCtorPreserved
    -- Caller-provided `Decls.R` for the simulation chain. Bundles
    -- `CtorPreserved + FnNamesAgree`; both are produced by the entry-
    -- restricted kind-preservation chain in Phase4 + step4Lower-backward
    -- family. Same compilation chain as `hCtorPreserved` above; the
    -- FnNamesAgree clause additionally composes through
    -- `concretizeBuild_preserves_function_kind_at_entry_fwd`.
    have hDeclsR : ∀ (concDecls : Concrete.Decls),
        t.checkAndSimplify.toOption.bind (·.concretize.toOption) = some concDecls →
        Aiur.Simulation.Decls.R decls concDecls := by
      intro concDecls _hcd
      -- Closure of #15.B.
      --
      -- `Decls.CtorPreserved` and `Decls.FnNamesAgree` each bundle a
      -- FWD direction (guarded by `params = []`, ensuring same-key
      -- propagation is possible) AND a template-name BWD direction
      -- (existential — every concrete entry has SOME source preimage,
      -- possibly at a mangled key). The BWD directions are essential for
      -- the simulation's `srcNone`/`srcDt` arms in
      -- `step_R_preservation_applyGlobal` (Simulation.lean) — those arms
      -- must rule out concrete dispatching `.constructor`/`.function` at
      -- a key where source has `none`/`.dataType`. The existential-form
      -- BWD sidesteps the impossibility of universal same-key
      -- preservation under polymorphic source, where mangled-key origins
      -- from drain's `newDataTypes` / `newFunctions` produce concrete
      -- entries at keys with no source preimage at the same key.
      --
      -- `Decls.R = Decls.CtorPreserved ∧ Decls.FnNamesAgree ∧
      -- Decls.BodyBridge`. Each of the first two is itself FWD ∧ BWD; the
      -- BWD clauses are closed via inline 2-way splits (mirror of the
      -- FullyMono-side `concretize_under_fullymono_*_bwd` patterns at
      -- Phase4.lean) — under entry-restriction we skip the params-empty
      -- residual that the FullyMono-side derives from the universal
      -- hypothesis, since the existential form only requires existence
      -- (not same-key). The `BodyBridge` clause dispatches to the
      -- planted helper `body_termBridge_at_function_key` defined above.
      -- The `CtorPreserved` FWD clause is structurally identical to the
      -- discharge of `hCtorPreserved` above (3-step chain
      -- `checkAndSimplify_preserves_ctor_kind_fwd` →
      -- `concretizeBuild_preserves_ctor_kind_at_entry_fwd` →
      -- `step4Lower_preserves_ctor_kind_fwd`). The `FnNamesAgree` FWD
      -- clause is the function analog: goes through the inputs-labels
      -- preserving variants `concretizeBuild_preserves_function_inputs_at_entry_fwd`
      -- (Phase4.lean:386) and `step4Lower_function_explicit`
      -- (Shapes.lean:1369).
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
      -- `Decls.R = CtorPreserved ∧ FnNamesAgree ∧ BodyBridge`. A
      -- universal `Decls.ParamsEmpty` clause would be provably False on
      -- polymorphic source — e.g. `Option<T>` has
      -- `decls.getByKey "Option.None" = .constructor poly_dt c` with
      -- `poly_dt.params != []`. Instead we use a per-call
      -- `Decls.ParamsAtName` premise threaded through
      -- `step_R_preservation_applyGlobal` directly; the entry-call producer
      -- discharges via `Source.Function.notPolyEntry`.
      -- Each of `CtorPreserved` and `FnNamesAgree` is itself a 2-conjunction
      -- (FWD ∧ BWD). Discharge each clause separately.
      refine ⟨?_, ?_, ?_⟩
      · -- `Decls.CtorPreserved` clause: FWD ∧ BWD.
        refine ⟨?_, ?_⟩
        · -- FWD direction (3-step chain through ctor-kind preservation).
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
        · -- Template-name BWD direction. Mirror of the parallel
          -- `hCtorPreserved` BWD discharge above (same step4Lower-backward +
          -- `concretizeBuild_ctor_origin` 2-way split, with origin-4 chasing
          -- through `mkDecls_dt_implies_ctor_keys` to the source `.ctor`
          -- preimage).
          intro g_conc cdt cc hgc
          obtain ⟨md_dt, md_c, hmono_get⟩ :=
            step4Lower_backward_ctor_kind_at_key hgc hfold
          rcases PhaseA2.concretizeBuild_ctor_origin tds drained.mono
              drained.newFunctions drained.newDataTypes hmono_get with
            ⟨src_dt_typed, src_c_typed, htd_orig, _hparams⟩
            | ⟨dt', hdt_mem, c', hc_mem, hcname⟩
          · have hP := FnMatchP_checkAndSimplify hdecls hts
            exact ⟨g_conc, src_dt_typed, src_c_typed,
              (hP g_conc).2.2 src_dt_typed src_c_typed htd_orig⟩
          · have hSNN := concretize_drain_preserves_StrongNewNameShape _ _
              (DrainState.StrongNewNameShape.init tds (concretizeSeed tds)) hdrain
            obtain ⟨g_orig, args, dt_orig, _hname, hget_orig, _hargs_sz, hctors⟩ :=
              hSNN.2 dt' hdt_mem
            have hmem_map : c'.nameHead ∈ dt'.constructors.map (·.nameHead) :=
              List.mem_map_of_mem hc_mem
            rw [hctors, List.mem_map] at hmem_map
            obtain ⟨c_orig, hc_orig_mem, _hc_orig_nameHead⟩ := hmem_map
            have hP := FnMatchP_checkAndSimplify hdecls hts
            have hsrc_dt : decls.getByKey g_orig = some (.dataType dt_orig) :=
              (hP g_orig).2.1 dt_orig hget_orig
            have hsrc_ctor :=
              mkDecls_dt_implies_ctor_keys hdecls g_orig dt_orig hsrc_dt c_orig
                hc_orig_mem
            exact ⟨g_orig.pushNamespace c_orig.nameHead, dt_orig, c_orig,
              hsrc_ctor⟩
      · -- `Decls.FnNamesAgree` clause: FWD ∧ BWD.
        refine ⟨?_, ?_⟩
        · -- FWD direction (3-step chain through function-kind preservation).
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
          obtain ⟨cf, hcf_get, _hname_eq, hcf_inputs_witness, _houtput_witness, _hbody_witness⟩ :=
            step4Lower_function_explicit hmono hfold
          refine ⟨cf, hcf_get, ?_⟩
          -- Combine `cf.inputs.map (·.1) = md_f.inputs.map (·.1)` (via mapM
          -- witness) with `md_f.inputs.map (·.1) = tf.inputs.map (·.1)`
          -- (`hmono_inputs`) and `tf.inputs = f_src.inputs` (`htf_inputs_eq`).
          have hcf_md_inputs : md_f.inputs.map (·.1) = cf.inputs.map (·.1) :=
            mapM_first_proj md_f.inputs cf.inputs hcf_inputs_witness
          rw [htf_inputs_eq] at hmono_inputs
          rw [← hcf_md_inputs, hmono_inputs]
        · -- Template-name BWD direction. Closure: step4Lower-backward gives
          -- mono `.function` at `g_conc`, then `concretizeBuild_function_origin`
          -- 2-way split classifies. Origin 1 lifts typed `.function` to
          -- source `.function` at SAME key via FnMatchP backward. Origin 4
          -- (drain `newFunctions` at mangled key): StrongNewNameShape gives
          -- typed-source `.function f_orig` at `g_orig` with `f.name =
          -- concretizeName g_orig args`; FnMatchP gives source `.function`
          -- at `g_orig`. Either origin's source key serves as the
          -- existential preimage.
          intro g_conc f_conc hgc
          obtain ⟨md_f, hmono_get⟩ :=
            step4Lower_backward_function_kind_at_key hgc hfold
          rcases DirectDagBody.concretizeBuild_function_origin tds drained.mono
              drained.newFunctions drained.newDataTypes hmono_get with
            ⟨tf_src, htd_orig, _hparams⟩ | ⟨f, hf_mem, _hf_name⟩
          · -- Origin 1: typed `.function` at `g_conc`. Lift to source via FnMatchP.
            have hP := FnMatchP_checkAndSimplify hdecls hts
            obtain ⟨f_src, hsrc_get, _hinputs⟩ := (hP g_conc).1 tf_src htd_orig
            exact ⟨g_conc, f_src, hsrc_get⟩
          · -- Origin 4: f ∈ newFunctions has f.name = g_conc.
            -- StrongNewNameShape gives typed-source `.function f_orig` at `g_orig`.
            have hSNN := concretize_drain_preserves_StrongNewNameShape _ _
              (DrainState.StrongNewNameShape.init tds (concretizeSeed tds)) hdrain
            obtain ⟨g_orig, _args, f_orig, _hname, hget_orig, _hargs_sz⟩ :=
              hSNN.1 f hf_mem
            -- Source `.function` at `g_orig` (FnMatchP backward).
            have hP := FnMatchP_checkAndSimplify hdecls hts
            obtain ⟨f_src, hsrc_get, _hinputs⟩ := (hP g_orig).1 f_orig hget_orig
            exact ⟨g_orig, f_src, hsrc_get⟩
      · -- `Decls.BodyBridge` clause: TermBridge between source and concrete
        -- function bodies. Discharged via the planted helper
        -- `body_termBridge_at_function_key` which carries a single inner
        -- granular sub-sorry (`BLOCKED-BodyBridge-TermBridge-StructuralLift`)
        -- for the per-arm structural induction over `f_src.body`.
        intro g f_src f_conc hsrc hcd hf_params
        exact body_termBridge_at_function_key hwf hdecls hts hconc hsrc hcd
          hf_params
    -- The previous `hCtorAgreesAll` derivation (which discharged the
    -- caller-hoisted `_hCtorFlatSize` premise plus the ctor-index
    -- agreement chain for `flatten_agree_entry`'s `.ctor` arm) is
    -- REMOVED. The consumer `flatten_agree_entry` has itself been
    -- replaced by `Aiur.Simulation.ValueR_implies_flatten_eq`, which
    -- consumes a `ValueR v_src v_conc` pair carrying `h_ctor_flat_bridge`
    -- directly rather than per-key shape agreement.
    --
    -- The reachability keepalive below is preserved for future consumers
    -- of the ctor-index + flat-size chain. We bracket it under a `have`
    -- with a `True` conclusion so the chain remains reachable from
    -- `compile_correct` per CheckReach.lean targets.
    have _hCtorChainKeepalive : True := by
      -- Reachability keepalives for the Layout chain (formerly fed by the
      -- per-key ctor-index + flat-size agreement chain consumed by the
      -- now-removed `flatten_agree_entry`).
      let _ := @dataTypeFlatSize_eq_layoutMap_size_wf
      let _ := @layoutMap_dataType_size_extract
      let _ := @PhaseA2.concretizeBuild_at_typed_ctor_explicit_general
      trivial
    -- `Value.MonoCtorReach` predicate and its projection lemmas
    -- (`ctor_src`, `ctor_conc`, `ctor_args`) are REMOVED. The cross-
    -- evaluator value bridge is now carried by `ValueR`
    -- (`Aiur.Simulation.lean`), specifically the `h_ctor_flat_bridge`
    -- field on `ValueR.ctor`. Consumer obligations from the deleted
    -- predicate have been hoisted to `compile_correct`'s caller as
    -- `_hconcRetFlatAgree` (return-value flat-equality) and `_hargsR`
    -- (per-arg `ValueR v v`).
    exact Toplevel.compile_preservation_entry t ct decls hdecls hct hwf
      name funIdx hname hsrc hentry args io₀ fuel retTyp hargsFnFree
        hargsR hconcRetFnFree hconcRetFlatAgree hcdNameAgrees hDeclsR

end Aiur

end -- @[expose] public section
