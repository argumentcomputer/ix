module
public import Ix.Aiur.Proofs.DedupSound
public import Ix.Aiur.Proofs.LowerSoundControl
public import Ix.Aiur.Proofs.ConcretizeSound
public import Ix.Aiur.Proofs.SimplifySound
public import Ix.Aiur.Proofs.CheckSound
public import Ix.Aiur.Proofs.CompilerProgress
public import Ix.Aiur.Proofs.StructCompatible
public import Ix.Aiur.Proofs.ValueEqFlatten
public import Ix.Aiur.Proofs.Simulation
public import Ix.Aiur.Semantics.WellFormed
public import Ix.Aiur.Semantics.Relation

/-!
Top-level preservation.

Compose `Toplevel.compile_preservation` from Dedup, Lower, Concretize, and
Simplify soundness by transitivity of `InterpResultEq`, threading fuel /
`StructCompatible` / typing assumptions through the composition.

This is the preservation half of the top-level `compile_correct` theorem.
-/

public section

namespace Aiur

open Source

/-- Function-name → `FunIdx` lookup lifted to a `Global → Option Nat`. Used
both in `ValueEq` (to resolve `.fn` values to their call indices) and in the
statement of `compile_preservation`. -/
@[inline] def CompiledToplevel.globalFuncIdx (ct : CompiledToplevel) :
    Global → Option Nat :=
  fun g => ct.nameMap[g]?

/-!
### Signature-integration history (resolved)

Earlier rounds surfaced three signature-level mismatches between per-pass
preservation claims and what the composition needs. All have been resolved:

- **Concretize value-level equivalence**: `Typed.Decls.concretize_preservation`
  now returns `flattenValue`-equality + `IOBuffer.equiv` (not just IOBuffer).
- **Lower funcIdx remap**: `Toplevel.compile_preservation` takes FnFree
  hypotheses (`hargsFnFree`, `hconcRetFnFree`); `ValueEq.transport_remap` +
  `InterpResultEq.transport_remap_of_src_fnFree` live in `LowerShared.lean`.
- **Dedup constrained-flag irrelevance**: `Bytecode.Eval.runFunction_constrained_irrelevant`
  lives in `DedupSound.lean`.
-/

/-! ## Local aux. -/

namespace Step1_3Body

open Source

/-! ## Source-side invariant: every `.constructor dt c` has `dt.params = []`.

Mirror of `SrcDtParamsMonoP` for `.constructor` entries. -/

private def SrcCtorDtParamsMonoP (d : Source.Decls) : Prop :=
  ∀ k dt c, d.getByKey k = some (.constructor dt c) → dt.params = []

private def TdCtorDtParamsMatchP (d : Source.Decls) (td : Typed.Decls) : Prop :=
  ∀ k dt c, td.getByKey k = some (.constructor dt c) →
    d.getByKey k = some (.constructor dt c)



end Step1_3Body

/-! ### `concretize_keys_of_mono` — decomposed.

Two sub-lemmas:
1. `concretize_steps_1_3_keys`: Steps 1–3 of `concretize` under `FullyMonomorphic`
   produce a `monoDecls : Typed.Decls` whose keys match `typedDecls`.
2. `concretize_step_4_keys_of_fold`: Step 4 (an insert-only `foldlM`) preserves
   keys from `monoDecls` to `concDecls`.

The composition still has one inline sorry: extracting the Step 4 fold equation
from `_hconc`. Full closure requires refactoring `concretize`'s imperative
Steps 1–3 (`let mut`/`while`/`for`) into pure functional form. -/





private theorem CompiledToplevel.getFuncIdx_eq (ct : CompiledToplevel) (name : Lean.Name) :
    ct.getFuncIdx name = ct.nameMap[Global.mk name]? := rfl

private theorem CompiledToplevel.globalFuncIdx_eq (ct : CompiledToplevel) (g : Global) :
    ct.globalFuncIdx g = ct.nameMap[g]? := rfl

-- `Toplevel.compile_preservation` (FullyMono predecessor of
-- `compile_preservation_entry`) is REMOVED. The entry-restricted variant's
-- body really composes through `concretize_preserves_runFunction_entry`
-- and the entry-bridge variants. The previous theorem had the same
-- conclusion but consumed `FullyMonomorphic t` and routed through the
-- orphan `flatten_agree_under_fullymono` + `Lower.compile_preservation`
-- + `Typed.Decls.concretize_preservation` chain.

/-! ### Wire A (REAL composition) — entry-restricted concretize preservation.

`concretize_preserves_runFunction_entry`: an entry-restricted variant of S3
(`concretize_preserves_runFunction`) whose body REALLY composes through the
simulation infrastructure (`Aiur.Simulation.concretize_runFunction_simulation`).

Path B from the wire spec: rather than cascading new hypotheses through S3
and its caller `Typed.Decls.concretize_preservation`, we add a parallel
entry-restricted theorem that:
- Takes `f_src : Source.Function` + `f_src.entry = true` + matched-inputs
  + per-arg `Value.FnFree` (the four "Wire B bridges" S3 lacks);
- Derives `hcompat : decls ↔ concDecls (none-iff)` from
  `namespace_preservation hdecls hts hconc hmono` (composition of
  `checkAndSimplify_keys` with `concretize_keys_of_mono`);
- Resolves `concDecls.getByKey name` to a function shape via a bridge
  helper (sorry: shape preservation under FullyMono — concretize keeps
  source-`.function` keys as concrete-`.function`);
- Hands off to `concretize_runFunction_simulation` for the actual
  simulation chain (`entry_R_initial` → `step_R_preservation_applyGlobal`
  → `ValueR_implies_flatten_eq` + `StateR.2`).

Existing S3 + its `Typed.Decls.concretize_preservation` wrapper are
unchanged — non-entry callers still compile. The entry chain
(`compile_preservation_entry`) consumes this new theorem.
-/





/-- **Wire A — REAL composition.** Entry-restricted concretize preservation,
body composes directly through `Aiur.Simulation.concretize_runFunction_simulation`.

Public delegate for entry-call sites. Takes the per-entry compatibility +
function-pair witnesses directly (no `FullyMonomorphic t` hypothesis):
- `hcompat`: name-space `none-iff` between source and concrete decls.
- `f_src` / `f_conc`: matched function pair at `name` in both decls.
- `hentry`: source-side `entry = true`.
- `h_inputs_match`: input-name lists agree pointwise.
- `hargsFnFree`: caller args contain no `.fn` values.

Body is a SINGLE call into `concretize_runFunction_simulation`. -/
theorem concretize_preserves_runFunction_entry
    {decls : Source.Decls} {concDecls : Concrete.Decls}
    (name : Global) (f_src : Source.Function) (f_conc : Concrete.Function)
    (hsrc : decls.getByKey name = some (.function f_src))
    (hf_conc : concDecls.getByKey name = some (.function f_conc))
    (hentry : f_src.entry = true)
    (h_inputs_match : f_src.inputs.map (·.1) = f_conc.inputs.map (·.1))
    (args : List Value) (io₀ : IOBuffer) (fuel : Nat)
    (funcIdx : Global → Option Nat)
    (hargsFnFree : ∀ v ∈ args, Value.FnFree v)
    -- Per-arg `ValueR v v` self-witness, replacing a previous
    -- `hargsReach` + `h_flat_agree` pair. Caller-supplied; mechanical
    -- for FnFree-only first-order args via `ValueR.unit/.field/.pointer/
    -- .tuple/.array` constructors. Ctor args require an explicit
    -- `h_ctor_flat_bridge` from the caller.
    (hargsR : ∀ v ∈ args, Aiur.Simulation.ValueR decls concDecls funcIdx v v)
    -- Bundled `Decls.R` witness threaded into
    -- `concretize_runFunction_simulation`'s
    -- `step_R_preservation_applyGlobal` call. Producer at
    -- `compile_preservation_entry` discharges from the compilation chain.
    (hDeclsR : Aiur.Simulation.Decls.R decls concDecls) :
    match Source.Eval.runFunction decls name args io₀ fuel,
          Concrete.Eval.runFunction concDecls name args io₀ fuel with
    | .ok (v₁, io₁), .ok (v₂, io₂) =>
        flattenValue decls funcIdx v₁ = Concrete.flattenValue concDecls funcIdx v₂
          ∧ IOBuffer.equiv io₁ io₂
    | .error _, .error _ => True
    | _, _ => False :=
  Aiur.Simulation.concretize_runFunction_simulation
    (decls := decls) (concDecls := concDecls) (funcIdx := funcIdx)
    name f_src f_conc hsrc hf_conc hentry h_inputs_match
    args io₀ fuel hargsFnFree hargsR hDeclsR

/-! ### Wire B — entry-restricted bridge variants of `_under_fullymono` callees.

Each bridge below is the entry-restricted parallel of an existing
`_under_fullymono` lemma. They take `WellFormed t` plus a witness that the
caller's specific function has `entry = true` (carried via the
`_hentry_witness` predicate below) instead of a global
`FullyMonomorphic t` hypothesis. Their bodies are stub `sorry`s with
documented closure paths; downstream `compile_preservation_entry` and
`compile_progress_entry` compose through them. -/

/-- Witness shape for the entry hypothesis as it appears at top level: there
exists a function in `decls` keyed at `name` with `entry = true`. Used as the
common entry obligation for the bridge stubs. -/
private def HasEntryFn (decls : Source.Decls) : Prop :=
  ∃ (name : Global) (f : Source.Function),
    decls.getByKey name = some (.function f) ∧ f.entry = true

/-! #### Genuine extraction lemma (F=1 leaf).

The named helper below extracts the contradiction at the heart of
`concretize_preserves_function_kind_entry_wf`: under source `.function f` at
`name`, the `monoDecls := concretizeBuild typedDecls drained.mono
drained.newFunctions drained.newDataTypes` carries `.function` at the same
key (the kind never flips to `.dataType`/`.constructor`).

F=1 BLOCKED on the structural argument: trace the three folds of
`concretizeBuild` (`fromSource` → `dtStep` → `fnStep`) over the typed table
(which by `FnMatchP_checkAndSimplify` has `.function` at `name`):

* `fromSource` arm at `(name, .function tf)`: enters the `.function` branch
  and inserts `.function` at `name` (since entry `f.params = []` ⟹ `tf.params
  = []`, the `params.isEmpty` guard fires).
* `dtStep` may overwrite at `dt.name` or `dt.name.pushNamespace c.nameHead`
  for `dt ∈ drained.newDataTypes`. By
  `concretize_drain_preserves_StrongNewNameShape`, every `dt ∈
  drained.newDataTypes` has `dt.name = concretizeName g #[…]` for some
  `g` keyed `.dataType` in typedDecls — the `dt.name = name` overwrite
  case requires `concretizeName g args = name` for a typed-`.dataType`
  source `g`, contradicting `_hwf.noNameCollisions` (which would force
  `g = name`, but typed has `.function` at `name`, not `.dataType`).
  The pushNamespace ctor case is similar.
* `fnStep` only inserts `.function`, never `.dataType`/`.constructor`. -/

/-- `concretizeBuild`'s output carries `.function` at a source function key
under `WellFormed` + entry hypotheses. Used to discharge both the `.dataType`
and `.constructor` cases of `concretize_preserves_function_kind_entry_wf` by
overdetermination (each call yields a function shape that contradicts the
non-`.function` hypothesis).

Delegates to `concretizeBuild_preserves_function_kind_at_entry_fwd`
(ConcretizeSound) after threading: source `.function f` at `name` →
typed `.function tf` at `name` (via `FnMatchP_checkAndSimplify`); `notPolyEntry`
+ `f.entry = true` ⟹ `f.params = []` ⟹ `tf.params = []` (via
`checkAndSimplify_preserves_params`); `_hwf.noNameCollisions` ⟹
`Typed.Decls.ConcretizeUniqueNames typedDecls`. -/
private theorem concretizeBuild_function_kind_at_function_key
    {t : Source.Toplevel} {decls : Source.Decls}
    {typedDecls : Typed.Decls} {concDecls : Concrete.Decls}
    {drained : DrainState}
    (hdecls : t.mkDecls = .ok decls)
    (hts : t.checkAndSimplify = .ok typedDecls)
    (hconc : typedDecls.concretize = .ok concDecls)
    (hdrain : concretizeDrain typedDecls (concretizeDrainFuel typedDecls)
      { pending := concretizeSeed typedDecls, seen := {}, mono := {},
        newFunctions := #[], newDataTypes := #[] } = .ok drained)
    (hwf : WellFormed t)
    (name : Global) {f : Source.Function}
    (hsrc : decls.getByKey name = some (.function f))
    (hentry : f.entry = true) :
    ∃ md_f, (concretizeBuild typedDecls drained.mono
      drained.newFunctions drained.newDataTypes).getByKey name =
        some (.function md_f) := by
  -- 1. Lift source `.function f` at `name` to typed `.function tf` at `name`.
  have hP := FnMatchP_checkAndSimplify hdecls hts
  obtain ⟨tf, htyped⟩ : ∃ tf, typedDecls.getByKey name = some (.function tf) := by
    -- `FnMatchP` (typed-direction) gives a typed entry at `name` with shape
    -- matching source. Use the source→typed bridge: any source `.function f`
    -- at `name` has typed `.function tf` at `name` with `tf.inputs = f.inputs`.
    have hkeys :=
      (checkAndSimplify_keys_local hdecls hts name)
    have hsrc_ne : decls.getByKey name ≠ none := by rw [hsrc]; simp
    have htd_ne : typedDecls.getByKey name ≠ none := hkeys.mp hsrc_ne
    cases htd : typedDecls.getByKey name with
    | none => exact absurd htd htd_ne
    | some d =>
      cases d with
      | function tf => exact ⟨tf, rfl⟩
      | dataType dt =>
        exfalso
        have hsrc_dt : decls.getByKey name = some (.dataType dt) :=
          (hP name).2.1 dt htd
        rw [hsrc] at hsrc_dt; cases hsrc_dt
      | constructor dt c =>
        exfalso
        have hsrc_ctor : decls.getByKey name = some (.constructor dt c) :=
          (hP name).2.2 dt c htd
        rw [hsrc] at hsrc_ctor; cases hsrc_ctor
  -- 2. `notPolyEntry` + `hentry` ⟹ `f.params = []`. Then `checkAndSimplify_preserves_params`
  --    ⟹ `tf.params = []`.
  have hf_params : f.params = [] := by
    rcases f.notPolyEntry with hp | he
    · exact hp
    · rw [he] at hentry; cases hentry
  have htf_params : tf.params = [] := by
    rw [checkAndSimplify_preserves_params hdecls hts hsrc htyped, hf_params]
  -- 3. Extract `noNameCollisions` from `hwf` and apply the main lemma.
  have hUniqueNames : Typed.Decls.ConcretizeUniqueNames typedDecls :=
    hwf.noNameCollisions typedDecls hts
  exact concretizeBuild_preserves_function_kind_at_entry_fwd
    hdecls hts hdrain hconc hUniqueNames htyped htf_params

/-- **Wire B bridge (entry-restricted).** Shape preservation: under
`WellFormed t` + `HasEntryFn` for an entry name, the source `.function`
shape at that name persists through `concretize` to a `.function` on the
concrete side (kind never flips to `.dataType`/`.constructor`).

Entry-restricted parallel of `concretize_preserves_function_kind_fwd`
(FullyMono variant); takes `WellFormed` plus an entry witness instead.

Closure path: `concretize_drain_preserves_StrongNewNameShape` +
`concretizeSeed` invariant — entries are seeded with `(name, #[])` and
drain emits `.function` declarations at the unrenamed key
(`concretizeName name #[] = name` since entries have `params = []` via
`notPolyEntry`). -/
private theorem concretize_preserves_function_kind_entry_wf
    {t : Source.Toplevel} {decls : Source.Decls}
    {typedDecls : Typed.Decls} {concDecls : Concrete.Decls}
    (hdecls : t.mkDecls = .ok decls)
    (hts : t.checkAndSimplify = .ok typedDecls)
    (hconc : typedDecls.concretize = .ok concDecls)
    (_hwf : WellFormed t)
    (name : Global) {f : Source.Function}
    (hsrc : decls.getByKey name = some (.function f))
    (hentry : f.entry = true) :
    ∃ f_conc : Concrete.Function,
      concDecls.getByKey name = some (.function f_conc) := by
  -- Closure path:
  -- 1. Unfold `hconc` to expose `monoDecls := concretizeBuild typedDecls
  --    drained.mono drained.newFunctions drained.newDataTypes` and the foldlM
  --    `monoDecls.foldlM step4Lower (init := default) = .ok concDecls`.
  -- 2. Extract `monoDecls.getByKey name = some (.function md_f)` via the named
  --    helper `concretizeBuild_function_kind_at_function_key`.
  -- 3. Lift forward through `step4Lower` via
  --    `step4Lower_preserves_function_kind_fwd` to get the concrete function.
  have hconc_orig := hconc
  unfold Typed.Decls.concretize at hconc
  simp only [bind, Except.bind] at hconc
  split at hconc
  · cases hconc
  rename_i drained hdrain
  obtain ⟨md_f, hmd_f⟩ := concretizeBuild_function_kind_at_function_key
    (drained := drained) hdecls hts hconc_orig hdrain _hwf name hsrc hentry
  exact step4Lower_preserves_function_kind_fwd hmd_f hconc

/-- **Wire B bridge — entry-restricted.** Replaces the universal namespace-iff
form with a single-key existence claim for the specific entry function. The
universal form is structurally false for polymorphic source toplevels:
`concretizeBuild`'s `srcStep` skips polymorphic `.function` entries
(`tf.params ≠ []`), so polymorphic source decls have NO concrete-side image.
This entry-restricted form holds for any entry by routing through
`concretize_preserves_function_kind_entry_wf` (which itself derives
`concDecls.containsKey name` forward via insert-only properties of the three
`concretizeBuild` folds + `step4Lower` keys-iff). -/
private theorem namespace_preservation_entry
    {t : Source.Toplevel} {decls : Source.Decls}
    {typedDecls : Typed.Decls} {concDecls : Concrete.Decls}
    (hdecls : t.mkDecls = .ok decls)
    (hts : t.checkAndSimplify = .ok typedDecls)
    (hconc : typedDecls.concretize = .ok concDecls)
    (hwf : WellFormed t)
    (name : Global) {f : Source.Function}
    (hsrc : decls.getByKey name = some (.function f))
    (hentry : f.entry = true) :
    concDecls.getByKey name ≠ none := by
  obtain ⟨f_conc, hgc⟩ :=
    concretize_preserves_function_kind_entry_wf hdecls hts hconc hwf name hsrc hentry
  rw [hgc]; exact Option.some_ne_none _

/-! #### Closure scaffolding for `concretize_preserves_entry_inputs_wf`.

Three named sub-pieces:

(P1) `step4Lower_function_inputs_locals_match_step` — F=0. Mechanical unfold
  of `step4Lower`'s function arm: when the concrete function inserted at
  `name` is `cf`, then `cf.inputs.map (·.1) = f.inputs.map (·.1)` because the
  inner `mapM` only translates types and re-pairs with the unchanged label.

(P2) `step4Lower_fold_function_inputs_locals_origin` — F=0. Fold-level
  inversion mirroring `step4Lower_fold_function_origin` but tracking the
  `inputs.map (·.1)` correspondence as part of the invariant: every
  `.function cf` in `concDecls` has an originating `.function f_mono` in
  `monoDecls` at the same key with `cf.inputs.map (·.1) = f_mono.inputs.map (·.1)`.

(P3) `monoDecls_entry_inputs_match_wf` — F=0. Bridges from `decls` to the
  typed-side monomorphic table produced by `concretize`'s Steps 1-3 with
  `f_mono.inputs.map (·.1) = f.inputs.map (·.1)` for the entry. Delegates to
  `concretizeBuild_preserves_function_inputs_at_entry_fwd` (ConcretizeSound).

Composition closes `concretize_preserves_entry_inputs_wf`. -/

/-- Auxiliary: any successful `mapM` translating types and re-pairing with the
unchanged label preserves `.1` projections. -/
private theorem inputs_mapM_preserves_locals
    (mono : Std.HashMap (Global × Array Typ) Global) :
    ∀ (l : List (Local × Typ)) (l' : List (Local × Concrete.Typ)),
      l.mapM (fun (lt : Local × Typ) => do
        let t' ← typToConcrete mono lt.2
        pure (lt.1, t')) = .ok l' →
      l'.map (·.1) = l.map (·.1)
  | [], l', h => by
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h; rfl
  | (lab, ty) :: xs, l', h => by
    simp only [List.mapM_cons, bind, Except.bind] at h
    split at h
    · cases h
    rename_i fx hfx
    split at h
    · cases h
    rename_i fxs hfxs
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    have ih := inputs_mapM_preserves_locals mono xs _ hfxs
    -- hfx : (match typToConcrete mono ty with | error → error | ok v → pure (lab, v)) = ok fx
    have hfx_fst : fx.1 = lab := by
      split at hfx
      · cases hfx
      rename_i v _
      simp only [pure, Except.pure, Except.ok.injEq] at hfx
      rw [← hfx]
    simp only [List.map_cons]
    rw [hfx_fst, ih]

/-- (P1) Per-step inputs-locals match for `step4Lower`'s function arm.
The inner `mapM (·.1)` only rewrites types; locals pass through unchanged. -/
private theorem step4Lower_function_inputs_locals_match_step
    {acc : Concrete.Decls} {name : Global} {f : Typed.Function}
    {r : Concrete.Decls}
    (hstep : step4Lower acc (name, .function f) = .ok r) :
    ∃ cf : Concrete.Function,
      r.getByKey name = some (.function cf) ∧
      cf.inputs.map (·.1) = f.inputs.map (·.1) := by
  unfold step4Lower at hstep
  simp only [bind, Except.bind, pure, Except.pure] at hstep
  split at hstep
  · cases hstep
  rename_i cInputs hInputs
  split at hstep
  · cases hstep
  rename_i cOutput hOutput
  split at hstep
  · cases hstep
  rename_i cBody hBody
  simp only [Except.ok.injEq] at hstep
  subst hstep
  refine ⟨_, IndexMap.getByKey_insert_self _ _ _, ?_⟩
  exact inputs_mapM_preserves_locals _ f.inputs cInputs hInputs

/-- (P2) Fold-level extraction: every `.function cf` in `concDecls` originates
from a `.function f_mono` in `monoDecls` at the same key, with matching
input-locals. Mirrors `step4Lower_fold_function_origin`'s pattern. -/
private theorem step4Lower_fold_function_inputs_locals_origin
    {monoDecls : Typed.Decls} {concDecls : Concrete.Decls}
    {g : Global} {cf : Concrete.Function}
    (hcf_get : concDecls.getByKey g = some (.function cf))
    (hfold : monoDecls.foldlM (init := default) step4Lower = .ok concDecls) :
    ∃ f_mono : Typed.Function,
      monoDecls.getByKey g = some (.function f_mono) ∧
      cf.inputs.map (·.1) = f_mono.inputs.map (·.1) := by
  let P : Concrete.Decls → Prop := fun acc =>
    ∀ g' cf', acc.getByKey g' = some (.function cf') →
      ∃ f' : Typed.Function,
        monoDecls.getByKey g' = some (.function f') ∧
        cf'.inputs.map (·.1) = f'.inputs.map (·.1)
  rw [IndexMap.indexMap_foldlM_eq_list_foldlM] at hfold
  have hPdefault : P (default : Concrete.Decls) := by
    intro g' cf' hget
    exfalso
    have hne : (default : Concrete.Decls).getByKey g' = none := by
      unfold IndexMap.getByKey
      show ((default : Concrete.Decls).indices[g']?).bind _ = none
      have : (default : Concrete.Decls).indices[g']? = none := by
        show ((default : Std.HashMap Global Nat))[g']? = none
        exact Std.HashMap.getElem?_empty
      rw [this]; rfl
    rw [hne] at hget; cases hget
  have hfinal : P concDecls := by
    apply List.foldlM_except_invariant monoDecls.pairs.toList _ _ _ _ hfold
    · exact hPdefault
    intro acc ⟨name, d⟩ acc' hxmem hstep hPacc
    intro g' cf' hget
    cases d with
    | function f =>
      obtain ⟨cf_step, hcf_step_get, hcf_step_in⟩ :=
        step4Lower_function_inputs_locals_match_step hstep
      by_cases hkn : (name == g') = true
      · have hkEq : name = g' := LawfulBEq.eq_of_beq hkn
        subst hkEq
        rw [hcf_step_get] at hget
        simp only [Option.some.injEq, Concrete.Declaration.function.injEq] at hget
        subst hget
        refine ⟨f, IndexMap.getByKey_of_mem_pairs _ _ _ hxmem, hcf_step_in⟩
      · have hne : (name == g') = false := Bool.not_eq_true _ |>.mp hkn
        unfold step4Lower at hstep
        simp only [bind, Except.bind, pure, Except.pure] at hstep
        split at hstep
        · cases hstep
        split at hstep
        · cases hstep
        split at hstep
        · cases hstep
        simp only [Except.ok.injEq] at hstep
        subst hstep
        rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
        exact hPacc g' cf' hget
    | dataType dt =>
      unfold step4Lower at hstep
      simp only [bind, Except.bind, pure, Except.pure] at hstep
      split at hstep
      · cases hstep
      simp only [Except.ok.injEq] at hstep
      subst hstep
      by_cases hkn : (name == g') = true
      · have hkEq : name = g' := LawfulBEq.eq_of_beq hkn
        subst hkEq
        rw [IndexMap.getByKey_insert_self] at hget
        cases hget
      · have hne : (name == g') = false := Bool.not_eq_true _ |>.mp hkn
        rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
        exact hPacc g' cf' hget
    | constructor dt c =>
      unfold step4Lower at hstep
      simp only [bind, Except.bind, pure, Except.pure] at hstep
      split at hstep
      · cases hstep
      split at hstep
      · cases hstep
      simp only [Except.ok.injEq] at hstep
      subst hstep
      by_cases hkn : (name == g') = true
      · have hkEq : name = g' := LawfulBEq.eq_of_beq hkn
        subst hkEq
        rw [IndexMap.getByKey_insert_self] at hget
        cases hget
      · have hne : (name == g') = false := Bool.not_eq_true _ |>.mp hkn
        rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
        exact hPacc g' cf' hget
  exact hfinal g cf hcf_get

/-- (P3) Bridge: the typed-side mono table produced by `concretize`'s
Steps 1-3 carries an entry function whose `inputs.map (·.1)` matches the
source function's.

Closure path: source `.function f` at `name` lifts to typed `.function tf`
at `name` (via `checkAndSimplify_preserves_inputs`/`-_params`). Then the
strengthened entry-fwd helper
`concretizeBuild_preserves_function_inputs_at_entry_fwd` (ConcretizeSound)
extracts `f_mono` from `concretizeBuild`'s output at `name` with
`f_mono.inputs.map (·.1) = tf.inputs.map (·.1)`. Chaining through
`tf.inputs = f.inputs` gives the conclusion. -/
private theorem monoDecls_entry_inputs_match_wf
    {t : Source.Toplevel} {decls : Source.Decls}
    {typedDecls : Typed.Decls} {concDecls : Concrete.Decls}
    (hdecls : t.mkDecls = .ok decls)
    (hts : t.checkAndSimplify = .ok typedDecls)
    (hconc : typedDecls.concretize = .ok concDecls)
    (hwf : WellFormed t)
    (name : Global) {f : Source.Function}
    (hsrc : decls.getByKey name = some (.function f))
    (hentry : f.entry = true) :
    ∃ (monoDecls : Typed.Decls) (f_mono : Typed.Function),
      monoDecls.foldlM (init := default) step4Lower = .ok concDecls ∧
      monoDecls.getByKey name = some (.function f_mono) ∧
      f_mono.inputs.map (·.1) = f.inputs.map (·.1) := by
  -- Step 1: Unfold `Typed.Decls.concretize` to expose `monoDecls` + foldlM eq.
  have hconc_orig := hconc
  unfold Typed.Decls.concretize at hconc
  simp only [bind, Except.bind] at hconc
  split at hconc
  · cases hconc
  rename_i drained hdrain
  -- Step 2: Get the typed function `tf` at `name` (key preservation).
  have htypedNe : typedDecls.getByKey name ≠ none := by
    have hkeys := checkAndSimplify_keys_local hdecls hts name
    exact hkeys.mp (by rw [hsrc]; exact Option.some_ne_none _)
  -- Source `f.entry = true` ⟹ `f.params = []` via `notPolyEntry`.
  have hfparams : f.params = [] := by
    rcases f.notPolyEntry with h | h
    · exact h
    · rw [h] at hentry; cases hentry
  -- The typed function at `name` shares `f`'s inputs and has `params = []`.
  obtain ⟨tf, htyped, hinputs⟩ : ∃ tf,
      typedDecls.getByKey name = some (.function tf) ∧ tf.inputs = f.inputs := by
    match htd : typedDecls.getByKey name with
    | none => exact absurd htd htypedNe
    | some (.function tf) =>
      exact ⟨tf, rfl, checkAndSimplify_preserves_inputs hdecls hts hsrc htd⟩
    | some (.dataType dt) =>
      exfalso
      have hP := FnMatchP_checkAndSimplify hdecls hts
      have := (hP name).2.1 dt htd
      rw [hsrc] at this; cases this
    | some (.constructor dt c) =>
      exfalso
      have hP := FnMatchP_checkAndSimplify hdecls hts
      have := (hP name).2.2 dt c htd
      rw [hsrc] at this; cases this
  have htfparams : tf.params = [] := by
    rw [checkAndSimplify_preserves_params hdecls hts hsrc htyped, hfparams]
  -- Step 3: extract `f_mono` from `concretizeBuild`'s output at `name` whose
  -- `inputs.map (·.1) = tf.inputs.map (·.1)`, via the strengthened entry-fwd
  -- helper `concretizeBuild_preserves_function_inputs_at_entry_fwd`.
  have hUniqueNames : Typed.Decls.ConcretizeUniqueNames typedDecls :=
    hwf.noNameCollisions typedDecls hts
  obtain ⟨f_mono, hmono_get, hmono_in⟩ :=
    concretizeBuild_preserves_function_inputs_at_entry_fwd
      hdecls hts hdrain hconc_orig hUniqueNames htyped htfparams
  refine ⟨_, f_mono, hconc, hmono_get, ?_⟩
  rw [hmono_in, hinputs]

/-- **Wire B bridge (entry-restricted).** Input-locals preservation: under
`WellFormed t` + entry witness, the source and concretized function at
the entry name have the same input-local-name lists.

Entry-restricted parallel of `concretize_preserves_entry_inputs`
(FullyMono variant); takes `WellFormed` plus the entry witness instead.

Closure path: composition of
- `monoDecls_entry_inputs_match_wf` (P3, F=0),
- `step4Lower_fold_function_inputs_locals_origin` (P2, F=0),
which together give `f_conc.inputs.map (·.1) = f_mono.inputs.map (·.1) =
f.inputs.map (·.1)`. -/
private theorem concretize_preserves_entry_inputs_wf
    {t : Source.Toplevel} {decls : Source.Decls}
    {typedDecls : Typed.Decls} {concDecls : Concrete.Decls}
    (hdecls : t.mkDecls = .ok decls)
    (hts : t.checkAndSimplify = .ok typedDecls)
    (hconc : typedDecls.concretize = .ok concDecls)
    (hwf : WellFormed t)
    (name : Global) {f : Source.Function} {f_conc : Concrete.Function}
    (hsrc : decls.getByKey name = some (.function f))
    (hconcF : concDecls.getByKey name = some (.function f_conc))
    (hentry : f.entry = true) :
    f.inputs.map (·.1) = f_conc.inputs.map (·.1) := by
  obtain ⟨monoDecls, f_mono, hfold, hmd_get, hmd_in⟩ :=
    monoDecls_entry_inputs_match_wf hdecls hts hconc hwf name hsrc hentry
  obtain ⟨f_mono', hmd_get', hcfin⟩ :=
    step4Lower_fold_function_inputs_locals_origin hconcF hfold
  rw [hmd_get'] at hmd_get
  simp only [Option.some.injEq, Typed.Declaration.function.injEq] at hmd_get
  subst hmd_get
  rw [← hmd_in, ← hcfin]

-- `flatten_agree_entry` and its sub-bridge `flatten_agree_entry_ctor_bridge`
-- are REMOVED. Their job — bridging
-- `flatten decls v = Concrete.flatten concDecls v` on a single value v —
-- relied on `Value.MonoCtorReach decls concDecls v`, which is provably
-- False on polymorphic-mangled-key concrete-eval results. The bridge has
-- been replaced by `Aiur.Simulation.ValueR_implies_flatten_eq`, which
-- consumes a `ValueR v_src v_conc` pair (cross-evaluator) instead of a
-- single-value MonoCtorReach predicate. Callers thread `ValueR` pairs
-- through the simulation chain directly; the
-- `h_ctor_flat_bridge` field on `ValueR.ctor` carries the literal
-- `.ctor`-envelope flatten-equality across source/concrete decls. See
-- `Simulation.lean` for the value-bridging strategy.

/-- **Wire B bridge.** Entry-restricted variant of
`compile_ok_implies_struct_compatible`. Body delegates to the StructCompatible
record builder in `Proofs/StructCompatible.lean`, which discharges three of
four conjuncts directly and routes `input_layout_matches` through a single
named entry-bridge stub (`compile_ok_input_layout_matches_entry`). -/
private theorem compile_ok_implies_struct_compatible_entry
    {t : Source.Toplevel} {ct : CompiledToplevel} {decls : Source.Decls}
    (hdecls : t.mkDecls = .ok decls)
    (hct : t.compile = .ok ct)
    (hwf : WellFormed t)
    (hentry : HasEntryFn decls) :
    StructCompatible decls ct.bytecode (fun g => ct.nameMap[g]?) :=
  compile_ok_implies_struct_compatible_of_entry hdecls hct hwf hentry

/-- **Wire B bridge.** Entry-restricted variant of `Lower.compile_preservation`
(the FullyMono predecessor has been removed). Body is direct: thread
`hbc` through `toBytecode_function_extract` and call `Function_body_preservation`.
The underlying proof does NOT consume FullyMono — it only needs a `decls ↔ cd`
namespace correspondence (provided here by `namespace_preservation_entry`). -/
private theorem Lower.compile_preservation_entry
    {cd : Concrete.Decls} {bytecode : Bytecode.Toplevel}
    {preNameMap : Std.HashMap Global Bytecode.FunIdx}
    {decls : Source.Decls}
    (hbc : cd.toBytecode = .ok (bytecode, preNameMap))
    (hNameAgrees : ∀ (key : Global) (f : Concrete.Function),
      (key, Concrete.Declaration.function f) ∈ cd.pairs.toList → key = f.name) :
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
  exact Function_body_preservation hbc hNameAgrees name f hname funIdx hfi args io₀ fuel retTyp

/-- **Preservation half — entry-restricted variant.**

Same conclusion as `Toplevel.compile_preservation`, but takes a per-entry
hypothesis `_hentry : f.entry = true` instead of a global
`FullyMonomorphic t`. Provable in principle:
`Source.Function.notPolyEntry` gives `f.params = []`; the transitive call
graph from `f` is fully monomorphized by `concretize`'s drain.

WIRE B: body composes through the entry-bridge variants
(`namespace_preservation_entry`, `compile_ok_implies_struct_compatible_entry`,
`Lower.compile_preservation_entry`) and through
`concretize_preserves_runFunction_entry` (which composes through
`Aiur.Simulation.concretize_runFunction_simulation`).

The `flatten_agree_entry` bridge — which relied on
`Value.MonoCtorReach` (provably False on polymorphic-mangled concrete-eval
results) — is REMOVED. The `.ctor`-arm flatten-equality across source and
concrete decls is now carried by the `h_ctor_flat_bridge` field of
`ValueR.ctor` (Simulation.lean). The return-value flatten-agreement is
hoisted as the caller-supplied `_hconcRetFlatAgree` premise. -/
theorem Toplevel.compile_preservation_entry
    (t : Source.Toplevel) (ct : CompiledToplevel) (decls : Source.Decls)
    (hdecls : t.mkDecls = .ok decls)
    (hct : t.compile = .ok ct)
    (hwf : WellFormed t) :
    ∀ (name : Lean.Name) (funIdx : Bytecode.FunIdx)
      (_hname : ct.getFuncIdx name = some funIdx)
      {f : Source.Function}
      (_hsrc : decls.getByKey (Global.mk name) = some (.function f))
      -- Entry restriction: by `Source.Function.notPolyEntry`, this forces
      -- `f.params = []` (no polymorphic public entries). Per-entry mono
      -- propagates through the transitive call graph via concretize's
      -- drained-mono table.
      (_hentry : f.entry = true)
      (args : List Value) (io₀ : IOBuffer) (fuel : Nat) (retTyp : Typ)
      (_hargsFnFree : ∀ v ∈ args, Value.FnFree v)
      -- Per-arg `ValueR v v` self-witness. Caller's discharge is
      -- mechanical for FnFree-only first-order args via `ValueR`
      -- structural constructors; ctor args require an explicit
      -- `h_ctor_flat_bridge` from the caller.
      (_hargsR : ∀ (concDecls : Concrete.Decls),
        t.checkAndSimplify.toOption.bind (·.concretize.toOption) = some concDecls →
        ∀ v ∈ args,
          Aiur.Simulation.ValueR decls concDecls ct.globalFuncIdx v v)
      -- Caller-provided: concrete returns are FnFree on the specific entry
      -- (type-soundness consequence of FO-return + RefClosed + TermRefsDt).
      (_hconcRetFnFree : ∀ (concDecls : Concrete.Decls) v io,
        t.checkAndSimplify.toOption.bind (·.concretize.toOption) = some concDecls →
        Concrete.Eval.runFunction concDecls (Global.mk name) args io₀ fuel = .ok (v, io) →
          Value.FnFree v)
      -- Direct flat-equality witness on the concrete return. Says: at
      -- the specific runFunction output `v_conc`, source-side and
      -- concrete-side flatten agree. This is precisely the bridge needed
      -- to compose the simulation output
      -- (`flatten v_src = Concrete.flatten v_conc`) with the bytecode
      -- preservation (`flatten v_conc = bytecode_output`) into the final
      -- `flatten v_src = bytecode_output`. Caller-discharged at
      -- `compile_correct` by composing entry-restricted concretize
      -- invariants on the specific return value.
      (_hconcRetFlatAgree : ∀ (concDecls : Concrete.Decls) v io,
        t.checkAndSimplify.toOption.bind (·.concretize.toOption) = some concDecls →
        Concrete.Eval.runFunction concDecls (Global.mk name) args io₀ fuel = .ok (v, io) →
          flattenValue decls ct.globalFuncIdx v =
            Concrete.flattenValue concDecls ct.globalFuncIdx v)
      -- Caller-provided: concretize produces nameAgrees structurally.
      (_hcdNameAgrees : ∀ (concDecls : Concrete.Decls),
        t.checkAndSimplify.toOption.bind (·.concretize.toOption) = some concDecls →
        ∀ (key : Global) (g : Concrete.Function),
          (key, Concrete.Declaration.function g) ∈ concDecls.pairs.toList → key = g.name)
      -- Caller-provided: simulation `Decls.R` (CtorPreserved + FnNamesAgree
      -- + BodyBridge). Replaces the placeholder `True` previously consumed
      -- by `step_R_preservation_applyGlobal`.
      (_hDeclsR : ∀ (concDecls : Concrete.Decls),
        t.checkAndSimplify.toOption.bind (·.concretize.toOption) = some concDecls →
        Aiur.Simulation.Decls.R decls concDecls),
      InterpResultEq decls ct.globalFuncIdx retTyp
        (Source.Eval.runFunction decls (Global.mk name) args io₀ fuel)
        (Bytecode.Eval.runFunction ct.bytecode funIdx
          (Flatten.args decls ct.globalFuncIdx args) io₀ fuel) := by
  intros name funIdx hname f hsrc hentry args io₀ fuel retTyp hargsFnFree
         hargsR hconcRetFnFree hconcRetFlatAgree hcdNameAgrees hDeclsR
  -- Entry witness shared by all bridge calls.
  have hHasEntry : HasEntryFn decls := ⟨Global.mk name, f, hsrc, hentry⟩
  have _hstruct :=
    compile_ok_implies_struct_compatible_entry hdecls hct hwf hHasEntry
  obtain ⟨typedDecls, concDecls, bytecodeRaw, preNameMap,
          hts, hconc, hbc⟩ := Source.Toplevel.compile_stages_of_ok hct
  let bytecodeDedup : Bytecode.Toplevel := bytecodeRaw.deduplicate.1
  let remap : Bytecode.FunIdx → Bytecode.FunIdx := bytecodeRaw.deduplicate.2
  have hBD : bytecodeDedup = bytecodeRaw.deduplicate.1 := rfl
  have hRM : remap = bytecodeRaw.deduplicate.2 := rfl
  have hdedup : bytecodeRaw.deduplicate = (bytecodeDedup, remap) := rfl
  simp only [Source.Toplevel.compile, hts, hconc, hbc, hdedup, bind, Except.bind,
             Except.mapError, pure, Except.pure] at hct
  injection hct with hct_eq
  have hct_bc : ct.bytecode =
      { bytecodeDedup with
          functions := bytecodeDedup.functions.mapIdx fun i f =>
            { f with constrained := bytecodeDedup.needsCircuit[i]! } } := by
    rw [← hct_eq]
  have hct_nm : ct.nameMap =
      preNameMap.fold (init := (∅ : Std.HashMap Global Bytecode.FunIdx))
        fun acc n i => acc.insert n (remap i) := by
    rw [← hct_eq]
  have hgfi : ∀ g, ct.globalFuncIdx g = (preNameMap[g]?).map remap := by
    intro g
    rw [CompiledToplevel.globalFuncIdx_eq, hct_nm, nameMap_value_via_remap preNameMap remap g]
  have hname' : ct.nameMap[Global.mk name]? = some funIdx := by
    rw [← CompiledToplevel.getFuncIdx_eq]; exact hname
  rw [hct_nm, nameMap_value_via_remap] at hname'
  match hpre : preNameMap[Global.mk name]? with
  | none =>
    rw [hpre] at hname'; simp at hname'
  | some preIdx =>
    rw [hpre, Option.map_some] at hname'
    have hfi_eq : funIdx = remap preIdx := (Option.some.injEq _ _).mp hname'.symm
    have h_d :
        Bytecode.Eval.runFunction ct.bytecode funIdx
            (Flatten.args decls ct.globalFuncIdx args) io₀ fuel =
          Bytecode.Eval.runFunction bytecodeDedup funIdx
            (Flatten.args decls ct.globalFuncIdx args) io₀ fuel := by
      rw [hct_bc]
      exact (Bytecode.Eval.runFunction_constrained_irrelevant bytecodeDedup
              bytecodeDedup.needsCircuit funIdx
              (Flatten.args decls ct.globalFuncIdx args) io₀ fuel).symm
    have h_wf_raw : WellFormedCallees bytecodeRaw :=
      toBytecode_produces_WellFormedCallees hbc
    have h_fix_raw :
        (let skeletons := bytecodeRaw.functions.map fun f =>
            (Bytecode.skeletonBlock f.body, f.layout)
         let (initClasses, _) := Bytecode.assignClasses skeletons
         let callees := bytecodeRaw.functions.map fun f =>
            Bytecode.collectCalleesBlock f.body
         let classes := Bytecode.partitionRefine initClasses callees
         let signatures := classes.mapIdx fun i cls =>
            (cls, callees[i]!.map (classes[·]!))
         (Bytecode.assignClasses signatures).1 = classes) :=
      Aiur.HFixRawCloseScratch.h_fix_raw_goal _
    have h_c_ok_transport :
        ∀ x, Bytecode.Eval.runFunction bytecodeRaw preIdx
                (Flatten.args decls ct.globalFuncIdx args) io₀ fuel = .ok x →
          Bytecode.Eval.runFunction bytecodeDedup funIdx
                (Flatten.args decls ct.globalFuncIdx args) io₀ fuel = .ok x := by
      intro x hx
      have := Bytecode.Toplevel.deduplicate_preservation bytecodeRaw h_wf_raw h_fix_raw
        preIdx (Flatten.args decls ct.globalFuncIdx args) io₀ fuel x
      simp only [← hBD, ← hRM] at this
      have hdedup_ok := this hx
      rw [hfi_eq]; exact hdedup_ok
    have hToOptionPre : t.checkAndSimplify.toOption.bind (·.concretize.toOption) = some concDecls := by
      simp [hts, hconc, Except.toOption]
    have hNameAgrees : ∀ (key : Global) (f : Concrete.Function),
        (key, Concrete.Declaration.function f) ∈ concDecls.pairs.toList → key = f.name :=
      hcdNameAgrees concDecls hToOptionPre
    have h_b_raw :=
      Lower.compile_preservation_entry (decls := decls) hbc
        hNameAgrees
        (Global.mk name) preIdx hpre args io₀ fuel retTyp
    -- Entry-restricted namespace preservation (replaces the universal-iff
    -- form of the FullyMono predecessor): asserts only that the entry name
    -- has a concrete-side image, true for any entry under `WellFormed`.
    have _hname_conc : concDecls.getByKey (Global.mk name) ≠ none :=
      namespace_preservation_entry hdecls hts hconc hwf (Global.mk name) hsrc hentry
    -- (2) Function-kind preservation: extract concrete-side function shape.
    -- Real composition through named bridge `concretize_preserves_function_kind_entry_wf`.
    have hf_conc : ∃ f_conc : Concrete.Function,
        concDecls.getByKey (Global.mk name) = some (.function f_conc) :=
      concretize_preserves_function_kind_entry_wf hdecls hts hconc hwf
        (Global.mk name) hsrc hentry
    obtain ⟨f_conc, hconcF⟩ := hf_conc
    -- (3) Inputs match: real composition through named bridge.
    have h_inputs_match : f.inputs.map (·.1) = f_conc.inputs.map (·.1) :=
      concretize_preserves_entry_inputs_wf hdecls hts hconc hwf
        (Global.mk name) hsrc hconcF hentry
    -- Args `ValueR` self-witnesses derived from caller hypothesis at
    -- this concretization.
    have hargsRConc : ∀ v ∈ args,
        Aiur.Simulation.ValueR decls concDecls ct.globalFuncIdx v v :=
      hargsR concDecls hToOptionPre
    -- Caller-provided `Decls.R decls concDecls` — the bundled simulation
    -- precondition required by `step_R_preservation_applyGlobal`.
    have hDeclsR_inst : Aiur.Simulation.Decls.R decls concDecls :=
      hDeclsR concDecls hToOptionPre
    -- (4) Apply Wire A: produces `Concrete.flattenValue concDecls` on RHS.
    have h_a_raw := concretize_preserves_runFunction_entry
      (Global.mk name) f f_conc hsrc hconcF hentry h_inputs_match
      args io₀ fuel ct.globalFuncIdx hargsFnFree hargsRConc hDeclsR_inst
    -- (5b) Bridge: convert `Concrete.flattenValue concDecls _ v₂` to
    -- `flattenValue decls _ v₂` via the caller-supplied
    -- `hconcRetFlatAgree` witness (replaces the previous
    -- `flatten_agree_entry v₂` derivation that consumed
    -- `MonoCtorReach v₂`).
    have h_a :
        match Source.Eval.runFunction decls (Global.mk name) args io₀ fuel,
              Concrete.Eval.runFunction concDecls (Global.mk name) args io₀ fuel with
        | .ok (v₁, io₁), .ok (v₂, io₂) =>
            flattenValue decls ct.globalFuncIdx v₁
              = flattenValue decls ct.globalFuncIdx v₂
              ∧ IOBuffer.equiv io₁ io₂
        | .error _, .error _ => True
        | _, _ => False := by
      revert h_a_raw
      cases hsrcRun : Source.Eval.runFunction decls (Global.mk name) args io₀ fuel with
      | error _ =>
        cases Concrete.Eval.runFunction concDecls (Global.mk name) args io₀ fuel with
        | error _ => intro h; exact h
        | ok _ => intro h; exact h
      | ok p₁ =>
        cases hconcRun : Concrete.Eval.runFunction concDecls (Global.mk name) args io₀ fuel with
        | error _ => intro h; exact h
        | ok p₂ =>
          obtain ⟨v₁, io₁⟩ := p₁
          obtain ⟨v₂, io₂⟩ := p₂
          intro ⟨hflat, hio⟩
          refine ⟨?_, hio⟩
          -- Bridge: caller-supplied `hconcRetFlatAgree` gives
          -- `flatten decls v₂ = Concrete.flatten concDecls v₂` directly.
          have hv₂_flat_agree :
              flattenValue decls ct.globalFuncIdx v₂ =
                Concrete.flattenValue concDecls ct.globalFuncIdx v₂ :=
            hconcRetFlatAgree concDecls v₂ io₂ hToOptionPre hconcRun
          rw [hflat]; exact hv₂_flat_agree.symm
    have h_args :
        Flatten.args decls ct.globalFuncIdx args =
          Flatten.args decls (fun g => preNameMap[g]?) args := by
      have hgfi_ext : ct.globalFuncIdx = (fun g => (preNameMap[g]?).map remap) := by
        funext g; exact hgfi g
      rw [Flatten.args_congr decls ct.globalFuncIdx (fun g => (preNameMap[g]?).map remap) args hgfi_ext]
      exact
        (Flatten.args_transport_remap_of_fnFree decls
          (fun g => preNameMap[g]?) remap args hargsFnFree).symm
    rw [← h_args] at h_b_raw
    have hConcRetFnFree :
        ∀ v io, Concrete.Eval.runFunction concDecls (Global.mk name) args io₀ fuel
                  = .ok (v, io) → Value.FnFree v :=
      fun v io hconc_ok => hconcRetFnFree concDecls v io hToOptionPre hconc_ok
    have hgfi_ext : ct.globalFuncIdx = (fun g => (preNameMap[g]?).map remap) := by
      funext g; exact hgfi g
    have h_b_remap :
        InterpResultEq decls (fun g => (preNameMap[g]?).map remap) retTyp
          (Concrete.Eval.runFunction concDecls (Global.mk name) args io₀ fuel)
          (Bytecode.Eval.runFunction bytecodeRaw preIdx
            (Flatten.args decls ct.globalFuncIdx args) io₀ fuel) :=
      InterpResultEq.transport_remap_of_src_fnFree
        (f := fun g => preNameMap[g]?) (remap := remap)
        hConcRetFnFree
        h_b_raw
    have h_b :
        InterpResultEq decls ct.globalFuncIdx retTyp
          (Concrete.Eval.runFunction concDecls (Global.mk name) args io₀ fuel)
          (Bytecode.Eval.runFunction bytecodeRaw preIdx
            (Flatten.args decls ct.globalFuncIdx args) io₀ fuel) := by
      rw [hgfi_ext]
      rw [Flatten.args_congr decls ct.globalFuncIdx
            (fun g => (preNameMap[g]?).map remap) args hgfi_ext] at h_b_remap
      exact h_b_remap
    have h_ab :
        InterpResultEq decls ct.globalFuncIdx retTyp
          (Source.Eval.runFunction decls (Global.mk name) args io₀ fuel)
          (Bytecode.Eval.runFunction bytecodeRaw preIdx
            (Flatten.args decls ct.globalFuncIdx args) io₀ fuel) :=
      InterpResultEq.trans
        (funcIdx := ct.globalFuncIdx) (retTyp := retTyp)
        (src := Source.Eval.runFunction decls (Global.mk name) args io₀ fuel)
        (mid := Concrete.Eval.runFunction concDecls (Global.mk name) args io₀ fuel)
        (bc  := Bytecode.Eval.runFunction bytecodeRaw preIdx
                  (Flatten.args decls ct.globalFuncIdx args) io₀ fuel)
        h_a h_b
    have h_cd_ok_transport :
        ∀ x, Bytecode.Eval.runFunction bytecodeRaw preIdx
                (Flatten.args decls ct.globalFuncIdx args) io₀ fuel = .ok x →
          Bytecode.Eval.runFunction ct.bytecode funIdx
                (Flatten.args decls ct.globalFuncIdx args) io₀ fuel = .ok x := by
      intro x hx
      rw [h_d]; exact h_c_ok_transport x hx
    unfold InterpResultEq at h_ab ⊢
    cases hsrc_out : Source.Eval.runFunction decls (Global.mk name) args io₀ fuel with
    | error _ =>
      cases hct_out : Bytecode.Eval.runFunction ct.bytecode funIdx
          (Flatten.args decls ct.globalFuncIdx args) io₀ fuel <;> trivial
    | ok sv =>
      cases hraw_out : Bytecode.Eval.runFunction bytecodeRaw preIdx
          (Flatten.args decls ct.globalFuncIdx args) io₀ fuel with
      | error _ =>
        rw [hsrc_out, hraw_out] at h_ab
        exact absurd h_ab (by intro h; exact h)
      | ok rv =>
        have hct_ok := h_cd_ok_transport rv hraw_out
        rw [hct_ok]
        rw [hsrc_out, hraw_out] at h_ab
        exact h_ab

end Aiur

end -- public section
