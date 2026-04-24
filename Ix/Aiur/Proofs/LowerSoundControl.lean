module
public import Ix.Aiur.Proofs.LowerSoundCore
public import Ix.Aiur.Proofs.LowerCalleesFromLayout
public import Ix.Aiur.Proofs.ConcretizeSound
public import Ix.Aiur.Compiler.Concretize
public import Ix.Aiur.Semantics.ConcreteEval
public import Ix.Aiur.Semantics.BytecodeEval
public import Ix.Aiur.Semantics.Flatten
public import Ix.Aiur.Semantics.Relation

/-!
Lower proof, full.

Extends the straight-line core to:
- `.match` in tail position.
- Non-tail `.match` via `Ctrl.matchContinue`, only for the let-RHS form matching
  `findNonTailMatch`. Matches in other positions are excluded by the
  `Concrete.Term` shape.
- `.ret` / `Ctrl.return` / `Ctrl.yield`.
- Function calls (`Op.call`); the `unconstrained` flag is semantically
  equivalent in both branches.
- `.store` / `.load` with width-bucketed memory.
- IO operations — the `IOBuffer` clause of the main theorem is discharged here.
- u8/u32 ops — `bv_decide` or a library of bitvector lemmas.
-/

public section

namespace Aiur

open Concrete

/-! ## Aux lemmas local to the full-term Lower proof. -/

/-! ### Decomposition of `Function_body_preservation`. -/

/-- Zero-fuel case. Trivial under the asymmetric `InterpResultEq`: concrete
side is `.error .outOfFuel` unconditionally at `fuel = 0`, and
`InterpResultEq (.error _) _ = True`. -/
private theorem Function_body_preservation_zero_fuel
    {cd : Concrete.Decls} {bytecode : Bytecode.Toplevel}
    {preNameMap : Std.HashMap Global Bytecode.FunIdx}
    {decls : Source.Decls}
    (_hbc : cd.toBytecode = .ok (bytecode, preNameMap))
    (name : Global) (f : Concrete.Function)
    (_hname : cd.getByKey name = some (.function f))
    (funIdx : Bytecode.FunIdx) (_hfi : preNameMap[name]? = some funIdx)
    (args : List Value) (io₀ : IOBuffer) (retTyp : Typ) :
    InterpResultEq decls (fun g => preNameMap[g]?) retTyp
      (Concrete.Eval.runFunction cd name args io₀ 0)
      (Bytecode.Eval.runFunction bytecode funIdx
        (Flatten.args decls (fun g => preNameMap[g]?) args) io₀ 0) := by
  simp only [Concrete.Eval.runFunction, Concrete.Eval.applyGlobal, InterpResultEq]
  split <;> trivial

/-- Successor-fuel case: reduces both sides to their per-block evaluators and
appeals to the (extended) `toIndex_preservation_core`. -/
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
        (Flatten.args decls (fun g => preNameMap[g]?) args) io₀ (fuel'+1)) := by
  -- BLOCKED ON:
  -- (1) `toIndex_preservation_core_extended` (LowerSoundCore.lean) is
  --     **decomposed** into per-arm sorries; current closure status:
  --       - 9 inherited core arms — **F=0**.
  --       - 4 arithmetic arms (.add/.sub/.mul/.eqZero) — **F=0**.
  --       - 10 u8/u32 arms — **F=0**.
  --       - 4 IO arms — **F=0**.
  --       - 1 `.store` arm — **F=0**.
  --       - `.tuple`/`.array` arms — F=0 modulo a width-distribution
  --         tail equation.
  --       - 6 collection/access arms (letLoad/proj/get/slice/set/load) —
  --         F=1; closure path is now decomposed using
  --         `interp_preserves_ValueHasTyp` (NEW witness producer, F=1
  --         in LowerShared.lean) + `flattenValue_size_of_ValueHasTyp` /
  --         `flattenValue_slice_at_offset` (S18/S19, F=1). Each arm has
  --         a 4-5-step blocked path documented inline.
  --       - 1 `.app` arm — central recursive obligation; Phase 4.
  -- (2) Tail-position handling for `.match` / `.ret` / `Ctrl.matchContinue` /
  --     `Ctrl.return` / `Ctrl.yield` — these never appear inside `toIndex`
  --     (it throws); they are produced by `Term.compile`'s block-level
  --     dispatch and need a separate `Block.compile_preservation` lemma
  --     (currently fused into this proof's body).
  -- (3) Input-bindings-agreement helper: `Flatten.args decls funcIdx args`
  --     vs the per-input `bindings` emitted by the input-foldlM in
  --     `Function.compile` (`inputs_foldlM_ok` already covers progress;
  --     preservation needs the layout/width parity at every input).
  -- (4) Threading `Concrete.Decls.RefClosed concDecls` and an env-typing
  --     hypothesis through `toIndex_preservation_core_extended`'s
  --     signature so the access arms can invoke
  --     `interp_preserves_ValueHasTyp`. Caller-side discharge of these
  --     hypotheses comes from
  --     `concretize_produces_refClosed` (already F=0) and the
  --     input-args typing invariant (NEW; needed in Function_compile
  --     entry).
  sorry

/-- Per-function preservation: `Concrete.Eval.runFunction` and the
compiled-bytecode evaluator agree on shared names. -/
theorem Function_body_preservation
    {cd : Concrete.Decls} {bytecode : Bytecode.Toplevel}
    {preNameMap : Std.HashMap Global Bytecode.FunIdx}
    {decls : Source.Decls}
    (hbc : cd.toBytecode = .ok (bytecode, preNameMap))
    (_hnames : ∀ g, decls.getByKey g ≠ none ↔ cd.getByKey g ≠ none)
    -- Structural invariant on `cd`: `.function` pairs store their key as
    -- `f.name`. Passes through to `toBytecode_function_extract`.
    (_hNameAgrees : ∀ (key : Global) (f : Concrete.Function),
      (key, Declaration.function f) ∈ cd.pairs.toList → key = f.name)
    (name : Global) (f : Concrete.Function)
    (hname : cd.getByKey name = some (.function f))
    (funIdx : Bytecode.FunIdx) (hfi : preNameMap[name]? = some funIdx)
    (args : List Value) (io₀ : IOBuffer) (fuel : Nat) (retTyp : Typ) :
    InterpResultEq decls (fun g => preNameMap[g]?) retTyp
      (Concrete.Eval.runFunction cd name args io₀ fuel)
      (Bytecode.Eval.runFunction bytecode funIdx
        (Flatten.args decls (fun g => preNameMap[g]?) args) io₀ fuel) := by
  obtain ⟨lm, hlm⟩ := toBytecode_layoutMap_ok hbc
  cases fuel with
  | zero =>
    exact Function_body_preservation_zero_fuel hbc name f hname funIdx hfi args io₀ retTyp
  | succ fuel' =>
    exact Function_body_preservation_succ_fuel hbc hlm name f hname funIdx hfi
      args io₀ fuel' retTyp

/-! ### Decomposition of `Function_compile_progress`. -/

/-- Step 1: `Function.compile` starts with `lm[f.name]?`; we need that lookup
to yield a `.function` entry. Closed modulo `Aiur.layoutMap_preserves_function_exists_aux`
(in `Proofs/LowerShared.lean`). -/
private theorem layoutMap_lookup_function
    {cd : Concrete.Decls} {lm : LayoutMap}
    (hlm : cd.layoutMap = .ok lm)
    (hNameAgrees : ∀ (key : Global) (f : Concrete.Function),
      (key, Declaration.function f) ∈ cd.pairs.toList → key = f.name)
    (hDtNameIsKey : ∀ (key : Global) (dt : Concrete.DataType),
      (key, Declaration.dataType dt) ∈ cd.pairs.toList → key = dt.name)
    (hCtorIsKey : ∀ (key : Global) (cdt : Concrete.DataType)
        (cc : Concrete.Constructor),
      (key, Declaration.constructor cdt cc) ∈ cd.pairs.toList →
      key = cdt.name.pushNamespace cc.nameHead)
    (hCtorPresent : ∀ (dtkey : Global) (dt : Concrete.DataType)
        (c : Concrete.Constructor),
      (dtkey, Declaration.dataType dt) ∈ cd.pairs.toList →
      c ∈ dt.constructors →
      ∃ cc, (dt.name.pushNamespace c.nameHead,
        Declaration.constructor dt cc) ∈ cd.pairs.toList)
    (name : Global) (f : Concrete.Function)
    (hname : cd.getByKey name = some (.function f)) :
    ∃ layout, lm[f.name]? = some (.function layout) := by
  have hkey_mem : ∃ key, (key, Declaration.function f) ∈ cd.pairs.toList
      ∧ (key == name) = true := by
    unfold IndexMap.getByKey at hname
    cases hidx : cd.indices[name]? with
    | none =>
      rw [hidx] at hname
      simp [bind, Option.bind] at hname
    | some i =>
      rw [hidx] at hname
      simp only [bind, Option.bind] at hname
      have hv := cd.validIndices name hidx
      have hi_lt : i < cd.pairs.size := hv.1
      have hkey_eq : (cd.pairs[i]'hi_lt).1 == name := hv.2
      have hget? : cd.pairs[i]? = some (cd.pairs[i]'hi_lt) := by
        rw [Array.getElem?_eq_some_iff]; exact ⟨hi_lt, rfl⟩
      rw [hget?] at hname
      simp only [Option.map_some] at hname
      have hsnd : (cd.pairs[i]'hi_lt).2 = Declaration.function f := Option.some.inj hname
      refine ⟨(cd.pairs[i]'hi_lt).1, ?_, hkey_eq⟩
      have hmem : cd.pairs[i]'hi_lt ∈ cd.pairs.toList :=
        Array.mem_toList_iff.mpr (Array.getElem_mem _)
      have hpair : ((cd.pairs[i]'hi_lt).1, Declaration.function f)
          = cd.pairs[i]'hi_lt := by
        rw [← hsnd]
      rw [hpair]; exact hmem
  obtain ⟨key, hmem, _⟩ := hkey_mem
  have hkey_eq_name : key = f.name := hNameAgrees key f hmem
  have hmem' : (f.name, Declaration.function f) ∈ cd.pairs.toList := by
    rw [← hkey_eq_name]; exact hmem
  exact layoutMap_preserves_function_exists_aux cd f.name f hNameAgrees hDtNameIsKey hCtorIsKey hCtorPresent hmem' ⟨lm, hlm⟩ lm hlm

/-- Step 2: `f.inputs.foldlM ... typSize lm typ` succeeds under `RefClosed cd`.
Closed modulo `Aiur.typSize_ok_of_refClosed_lm` (in `Proofs/LowerShared.lean`). -/
private theorem inputs_foldlM_ok
    {cd : Concrete.Decls} {lm : LayoutMap}
    (hlm : cd.layoutMap = .ok lm)
    (hrc : Concrete.Decls.RefClosed cd)
    (hdtkey : Concrete.Decls.DtNameIsKey cd)
    (hLKM : Concrete.Decls.LayoutKeysMatch cd)
    (f : Concrete.Function)
    (hname : ∃ name, cd.getByKey name = some (.function f)) :
    ∃ result : Nat × Std.HashMap Local (Array Bytecode.ValIdx),
      f.inputs.foldlM (init := ((0 : Nat), (default : Std.HashMap Local (Array Bytecode.ValIdx))))
        (fun (valIdx, bindings) (arg, typ) => do
          let len ← match typSize lm typ with
            | .error e => (throw e : Except String Nat)
            | .ok len => pure len
          let indices := Array.range' valIdx len
          pure (valIdx + len, bindings.insert arg indices))
      = (Except.ok result : Except String _) := by
  obtain ⟨name, hget⟩ := hname
  have hdeclRC : Concrete.Declaration.RefClosed cd (.function f) := hrc name _ hget
  have hinputsRC : ∀ lt ∈ f.inputs, Concrete.Typ.RefClosed cd lt.snd := hdeclRC.1
  apply List.foldlM_except_ok'
  intro acc p hp
  have hrcP : Concrete.Typ.RefClosed cd p.2 := hinputsRC p hp
  obtain ⟨n, hn⟩ := typSize_ok_of_refClosed_lm hlm hdtkey hLKM hrcP
  obtain ⟨valIdx, bindings⟩ := acc
  obtain ⟨arg, typ⟩ := p
  refine ⟨(valIdx + n, bindings.insert arg (Array.range' valIdx n)), ?_⟩
  simp only [hn, bind, Except.bind, pure, Except.pure]

/-- Step 3: block-level `Term.compile` succeeds from any starting state. This
is the headline extension of `toIndex_progress_core` to full `Term`. -/
private theorem body_compile_ok
    {cd : Concrete.Decls} {lm : LayoutMap}
    (_hlm : cd.layoutMap = .ok lm)
    (_hrc : Concrete.Decls.RefClosed cd)
    (f : Concrete.Function)
    (_hname : ∃ name, cd.getByKey name = some (.function f))
    (bindings : Std.HashMap Local (Array Bytecode.ValIdx))
    (state : CompilerState) :
    ∃ body state',
      (f.body.compile f.output lm bindings).run state =
        .ok body state' := by
  -- BLOCKED ON:
  -- (1) `toIndex_progress_core_extended` is **F=0** (LowerSoundCore).
  --     The toIndex-side blocker is gone; remaining work is block-level
  --     term-shape dispatch + IsCoreExtended-witness extraction.
  -- (2) Block-level dispatch in `Term.compile` for `.match`/`.ret`/
  --     `.matchContinue`/`.return`/`.yield`/`.letVar`-with-non-tail-
  --     `.match` RHS — these arms are NOT in `toIndex` (it throws on
  --     them); they're produced by `Term.compile`'s top dispatch
  --     (Lower.lean:352 `Concrete.Term.compile`). Closure path:
  --       (s1) Structural induction over `Concrete.Term` shape,
  --            generalizing over `bindings`/`state`/`yieldCtrl`.
  --       (s2) Each `.letVar`/`.letWild`-with-`.match`-RHS arm uses
  --            `Concrete.addCase` on each pattern + recurses on `bod`
  --            via the structural IH.
  --       (s3) Each non-match arm of `Term.compile` reduces to either
  --            `toIndex_progress_core_extended` (for the leaf `toIndex`
  --            call) OR recurses on the continuation via the IH.
  --       (s4) Tail `.ret` / `.match` / `Ctrl.return` / `Ctrl.yield`
  --            arms compile to `Bytecode.Ctrl`-tail forms; need a
  --            separate `Ctrl.compile_progress` helper.
  -- (3) `IsCoreExtended layoutMap f.body` derivation — needs an
  --     induction-on-shape from `Concrete.Term` carrying a
  --     `RefClosed`-derived `∃ n, typSize lm τ = .ok n` hypothesis at
  --     every `.proj`/`.get`/`.slice`/`.set`/`.letLoad`/`.load`/`.app`
  --     sub-term. Once the body is `IsCoreExtended`-typed, the access
  --     arms within `toIndex` succeed via `toIndex_progress_core_extended`.
  -- (4) `RefClosed cd` propagation through every `arg.typ` consulted by
  --     `.proj`/`.get`/`.slice`/`.set` — already provided via
  --     `_hrc : Concrete.Decls.RefClosed cd` at the call site; the
  --     IsCoreExtended derivation needs to extract per-`Typ`
  --     `typSize_ok_of_refClosed_lm` witnesses inside each carrier.
  sorry

/-- Per-function compile progress. Composed from the three steps above plus a
final `@[expose]`'d-`Function.compile` unfolding glue.

The signature adds `hNameAgrees` because Step 1 consults `lm[f.name]?` while
the caller only knows `cd.getByKey name = some (.function f)`. The link
`name = f.name` comes from the `.function` pair invariant (mirroring
`Function_body_preservation`). -/
theorem Function_compile_progress
    {t : Source.Toplevel} {tds : Typed.Decls} {cd : Concrete.Decls}
    (hmono : FullyMonomorphic t)
    (hts : t.checkAndSimplify = .ok tds)
    (hconc : tds.concretize = .ok cd)
    (hunique : Typed.Decls.ConcretizeUniqueNames tds)
    (lm : LayoutMap)
    (hlm : cd.layoutMap = .ok lm)
    (hNameAgrees : ∀ (key : Global) (f : Concrete.Function),
      (key, Declaration.function f) ∈ cd.pairs.toList → key = f.name)
    (hDtNameIsKey : ∀ (key : Global) (dt : Concrete.DataType),
      (key, Declaration.dataType dt) ∈ cd.pairs.toList → key = dt.name)
    (hCtorIsKey : ∀ (key : Global) (cdt : Concrete.DataType)
        (cc : Concrete.Constructor),
      (key, Declaration.constructor cdt cc) ∈ cd.pairs.toList →
      key = cdt.name.pushNamespace cc.nameHead)
    (hCtorPresent : ∀ (dtkey : Global) (dt : Concrete.DataType)
        (c : Concrete.Constructor),
      (dtkey, Declaration.dataType dt) ∈ cd.pairs.toList →
      c ∈ dt.constructors →
      ∃ cc, (dt.name.pushNamespace c.nameHead,
        Declaration.constructor dt cc) ∈ cd.pairs.toList)
    (htdDt : Typed.Decls.DtNameIsKey tds)
    (htdCtorPresent : Typed.Decls.CtorPresent tds)
    (name : Global) (f : Concrete.Function)
    (hname : cd.getByKey name = some (.function f)) :
    ∃ body lms, Concrete.Function.compile lm f = .ok (body, lms) := by
  have _hrc : Concrete.Decls.RefClosed cd :=
    concretize_produces_refClosed hmono hts hconc hunique htdDt htdCtorPresent
  -- Bridge pairs-form hypotheses to getByKey-form for `LayoutKeysMatch`.
  have hDtKey_gbk : Concrete.Decls.DtNameIsKey cd := by
    intro g dt hget
    have hmem : (g, Concrete.Declaration.dataType dt) ∈ cd.pairs.toList :=
      IndexMap.mem_pairs_of_getByKey cd g _ hget
    exact hDtNameIsKey g dt hmem
  have hLKM : Concrete.Decls.LayoutKeysMatch cd := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro g f' hget
      have hmem : (g, Concrete.Declaration.function f') ∈ cd.pairs.toList :=
        IndexMap.mem_pairs_of_getByKey cd g _ hget
      exact hNameAgrees g f' hmem
    · intro g dt hget
      have hmem : (g, Concrete.Declaration.dataType dt) ∈ cd.pairs.toList :=
        IndexMap.mem_pairs_of_getByKey cd g _ hget
      exact hDtNameIsKey g dt hmem
    · intro g dt c hget
      have hmem : (g, Concrete.Declaration.constructor dt c) ∈ cd.pairs.toList :=
        IndexMap.mem_pairs_of_getByKey cd g _ hget
      exact hCtorIsKey g dt c hmem
    · intro g dt hget c hc
      have hmem : (g, Concrete.Declaration.dataType dt) ∈ cd.pairs.toList :=
        IndexMap.mem_pairs_of_getByKey cd g _ hget
      obtain ⟨cc, hcmem⟩ := hCtorPresent g dt c hmem hc
      exact ⟨dt, cc, IndexMap.getByKey_of_mem_pairs cd _ _ hcmem⟩
  obtain ⟨_flayout, _hflayout⟩ :=
    layoutMap_lookup_function hlm hNameAgrees hDtNameIsKey hCtorIsKey hCtorPresent name f hname
  obtain ⟨⟨_vI, _bindings⟩, _hfold⟩ :=
    inputs_foldlM_ok hlm _hrc hDtKey_gbk hLKM f ⟨name, hname⟩
  obtain ⟨_body, _state', _hbody⟩ :=
    body_compile_ok hlm _hrc f ⟨name, hname⟩ _bindings
      { valIdx := _vI, selIdx := 0, ops := #[], degrees := Array.replicate _vI 1 }
  -- Normalize _hfold's do-body via body-congr to match Function.compile's
  -- post-unfold form.
  have _hfold' :
      f.inputs.foldlM
        (fun (x : Nat × Std.HashMap Local (Array Bytecode.ValIdx))
             (x_1 : Local × Concrete.Typ) =>
          match typSize lm x_1.snd with
          | .error e => (Except.error e : Except String _)
          | .ok len =>
            Except.ok (x.fst + len, x.snd.insert x_1.fst (Array.range' x.fst len)))
        (0, default) = .ok (_vI, _bindings) := by
    have := List.foldlM_congr_body
      (f := fun (x : Nat × Std.HashMap Local (Array Bytecode.ValIdx))
              (x_1 : Local × Concrete.Typ) =>
        match typSize lm x_1.snd with
        | .error e => (Except.error e : Except String _)
        | .ok len =>
          Except.ok (x.fst + len, x.snd.insert x_1.fst (Array.range' x.fst len)))
      (g := fun (valIdx, bindings) (arg, typ) => do
        let len ← match typSize lm typ with
          | .error e => (throw e : Except String Nat)
          | .ok len => pure len
        let indices := Array.range' valIdx len
        pure (valIdx + len, bindings.insert arg indices))
      (fun acc p => by obtain ⟨_, _⟩ := acc; obtain ⟨_, _⟩ := p; rfl)
      f.inputs (0, default)
    rw [this]
    exact _hfold
  -- Concrete.Function.compile desugars; thread the three steps through.
  show ∃ body lms, Concrete.Function.compile lm f = .ok (body, lms)
  unfold Concrete.Function.compile
  simp only [_hflayout, bind, Except.bind, pure, Except.pure]
  -- Split on the foldlM result.
  split
  · rename_i err herr
    exfalso
    have : (Except.error err : Except String _) = Except.ok (_vI, _bindings) :=
      herr.symm.trans _hfold'
    cases this
  · rename_i v hfv
    have hveq : v = (_vI, _bindings) := by
      have heq : (Except.ok v : Except String _) = Except.ok (_vI, _bindings) :=
        hfv.symm.trans _hfold'
      exact Except.ok.inj heq
    subst hveq
    simp only
    -- Now: split on EStateM.run of body.compile.
    split
    · rename_i e a hbe
      exfalso
      have : (EStateM.Result.error e a : EStateM.Result _ _ _) =
             EStateM.Result.ok _body _state' := hbe.symm.trans _hbody
      cases this
    · rename_i body a hbok
      have : (EStateM.Result.ok body a : EStateM.Result _ _ _) =
             EStateM.Result.ok _body _state' := hbok.symm.trans _hbody
      obtain ⟨hbeq, _⟩ := EStateM.Result.ok.inj this
      subst hbeq
      exact ⟨body, _, rfl⟩

/-- Full preservation for `Concrete.Decls.toBytecode`. This is the central
theorem of the full Lower proof; under the simultaneous-induction setup, it
depends on the inductive hypothesis being available at `fuel - 1` at every
`Op.call`.

Local invariant: the bytecode `map` slice at the compiled indices contains the
flattened form of every live binding.

Proof goes by induction on the `Concrete.Term` structure. The base cases are
inherited from `LowerSoundCore`. The inductive cases handle:
- `.match` and `.matchContinue` via case analysis on the scrutinee.
- `.app` via the IH at `fuel - 1`.
- `.store`/`.load` via width-bucket invariants.
- IO via equational reasoning on `IOBuffer`.
- u8/u32 via `bv_decide` or a library of bitvector lemmas. -/
theorem Lower.compile_preservation
    {cd : Concrete.Decls} {bytecode : Bytecode.Toplevel}
    {preNameMap : Std.HashMap Global Bytecode.FunIdx}
    {decls : Source.Decls}
    (hbc : cd.toBytecode = .ok (bytecode, preNameMap))
    -- `decls` and `cd` share a name space (Mismatch D bridge).
    (hnames : ∀ g, decls.getByKey g ≠ none ↔ cd.getByKey g ≠ none)
    -- Structural invariant: `.function` pairs store their key as `f.name`.
    (hNameAgrees : ∀ (key : Global) (f : Concrete.Function),
      (key, Declaration.function f) ∈ cd.pairs.toList → key = f.name) :
    ∀ (name : Global) (funIdx : Bytecode.FunIdx)
      (_hfi : preNameMap[name]? = some funIdx)
      (args : List Value) (io₀ : IOBuffer) (fuel : Nat) (retTyp : Typ),
      InterpResultEq decls (fun g => preNameMap[g]?) retTyp
        (Concrete.Eval.runFunction cd name args io₀ fuel)
        (Bytecode.Eval.runFunction bytecode funIdx
          (Flatten.args decls (fun g => preNameMap[g]?) args) io₀ fuel) := by
  intro name funIdx hfi args io₀ fuel retTyp
  obtain ⟨lm, hlm⟩ := toBytecode_layoutMap_ok hbc
  obtain ⟨f, _body, _lms, _hsz, hname, _hcomp, _hbody⟩ :=
    toBytecode_function_extract hbc hlm hNameAgrees name funIdx hfi
  exact Function_body_preservation hbc hnames hNameAgrees name f hname funIdx hfi args io₀ fuel retTyp

/-- Full progress for `Concrete.Decls.toBytecode`: when `cd` came from a
successful `concretize`, compilation succeeds.

Structural invariants on a `concretize`-produced `cd` that make every
`toBytecode` failure mode unreachable:
- no `.mvar` in any type (eliminated by zonking);
- no parametric `.app _ _` — every polymorphic use was specialized to
  `.ref mangledName`;
- every `.ref g` points at a datatype that also appears in `cd` (the
  worklist insert order guarantees closure);
- every `.app` call site resolves to a concretized `Concrete.Function`.

Proof outline: `cd.toBytecode` decomposes as (a) `cd.layoutMap` — total on
concretize-output decls (all `.ref g` resolve to datatypes); (b) a `foldlM`
over `cd.pairs` that, for each `.function` entry, calls `function.compile`
which ultimately invokes `toIndex`. The latter's per-term success follows
from `toIndex_progress_core` extended to the full `Concrete.Term` shape
(match/app/store/load/io/u8-u32). -/
theorem Lower.compile_progress
    {t : Source.Toplevel} {tds : Typed.Decls} {cd : Concrete.Decls}
    (hmono : FullyMonomorphic t)
    (hts : t.checkAndSimplify = .ok tds)
    (hconc : tds.concretize = .ok cd)
    (hacyclic : Typed.Decls.NoDirectDatatypeCycles tds)
    (hunique : Typed.Decls.ConcretizeUniqueNames tds)
    (hNameAgrees : ∀ (key : Global) (f : Concrete.Function),
      (key, Declaration.function f) ∈ cd.pairs.toList → key = f.name)
    (hDtNameIsKey : ∀ (key : Global) (dt : Concrete.DataType),
      (key, Declaration.dataType dt) ∈ cd.pairs.toList → key = dt.name)
    (hCtorIsKey : ∀ (key : Global) (cdt : Concrete.DataType)
        (cc : Concrete.Constructor),
      (key, Declaration.constructor cdt cc) ∈ cd.pairs.toList →
      key = cdt.name.pushNamespace cc.nameHead)
    (hCtorPresent : ∀ (dtkey : Global) (dt : Concrete.DataType)
        (c : Concrete.Constructor),
      (dtkey, Declaration.dataType dt) ∈ cd.pairs.toList →
      c ∈ dt.constructors →
      ∃ cc, (dt.name.pushNamespace c.nameHead,
        Declaration.constructor dt cc) ∈ cd.pairs.toList)
    (htdDt : Typed.Decls.DtNameIsKey tds)
    (htdCtorPresent : Typed.Decls.CtorPresent tds) :
    ∃ result, cd.toBytecode = .ok result := by
  have hdtkey_gbk : Concrete.Decls.DtNameIsKey cd := by
    intro g dt hget
    have hmem : (g, Concrete.Declaration.dataType dt) ∈ cd.pairs.toList :=
      IndexMap.mem_pairs_of_getByKey cd g _ hget
    exact hDtNameIsKey g dt hmem
  obtain ⟨lm, hlm⟩ :=
    concretize_layoutMap_progress hmono hts hconc hacyclic hunique hdtkey_gbk
      htdDt htdCtorPresent
  have hfn : ∀ name f, cd.getByKey name = some (.function f) →
      ∃ body lms, Concrete.Function.compile lm f = .ok (body, lms) :=
    fun name f hname =>
      Function_compile_progress hmono hts hconc hunique lm hlm hNameAgrees hDtNameIsKey
        hCtorIsKey hCtorPresent htdDt htdCtorPresent name f hname
  exact toBytecode_fold_progress lm hlm hfn

end Aiur

end
