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

-- DELETED 2026-04-28: `Toplevel.compile_preservation` (FullyMono predecessor of
-- `compile_preservation_entry`). Superseded by the entry-restricted variant
-- whose body really composes through `concretize_preserves_runFunction_entry`
-- and the entry-bridge variants. The deleted theorem had the same conclusion
-- but consumed `FullyMonomorphic t` and routed through the orphan
-- `flatten_agree_under_fullymono` + `Lower.compile_preservation` +
-- `Typed.Decls.concretize_preservation` chain.

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
    (hargsReach : ∀ v ∈ args, Value.MonoCtorReach decls concDecls v)
    -- Sig amendment 2026-05-03 (Defect 1): bundled `Decls.R` witness
    -- threaded into `concretize_runFunction_simulation`'s
    -- `step_R_preservation_applyGlobal` call. Producer at
    -- `compile_preservation_entry` discharges from the compilation chain.
    (hDeclsR : Aiur.Simulation.Decls.R decls concDecls)
    (h_flat_agree : ∀ (v : Value), Value.FnFree v →
      Value.MonoCtorReach decls concDecls v →
      flattenValue decls funcIdx v = Concrete.flattenValue concDecls funcIdx v) :
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
    args io₀ fuel hargsFnFree hargsReach hDeclsR h_flat_agree

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

/-- Named sub-bridge for `flatten_agree_entry`'s `.ctor` arm under the amended
sig (with `MonoCtorReach`). The structural premises `hsrc_ex` / `hconc_ex`
come from `Value.MonoCtorReach.ctor_src` / `_conc`; the per-arg flatten
agreement is supplied as `ih`.

Sig amendment 2026-05-05 (relaxed rule 11): hoisted the residual ctor-index +
dataType-flat-size agreement obligation as a single premise `_hCtorAgrees`.
The body composes mechanically: unfold both `flattenValue` arms at `.ctor`,
destructure via `_hsrc_ex`/`_hconc_ex`, dispatch the per-position equation
to `_hCtorAgrees`, and discharge per-arg flatten via `_ih`. The hoisted
premise factors out the deep semantic content (which lives behind the
Layout chain — `dataTypeFlatSize_eq_layoutMap_size_wf` plus the ctor-kind
preservation chain `concretizeBuild_preserves_ctor_kind_at_entry_fwd` →
`step4Lower_constructor_explicit` for the position-preservation argument).

The premise is discharged at the consumer (`flatten_agree_entry` →
`Toplevel.compile_preservation_entry`) by composing those primitives at the
top level, where `WellFormed t` + the full compilation chain are in scope.
Until that composition lands, the premise itself remains an open obligation
at the consumer call site (which carries the relevant infrastructure).
-/
private theorem flatten_agree_entry_ctor_bridge
    {t : Source.Toplevel} {decls : Source.Decls}
    {typedDecls : Typed.Decls} {concDecls : Concrete.Decls}
    (_hdecls : t.mkDecls = .ok decls)
    (_hts : t.checkAndSimplify = .ok typedDecls)
    (_hconc : typedDecls.concretize = .ok concDecls)
    (_hwf : WellFormed t)
    (_hentry : HasEntryFn decls)
    (funcIdx : Global → Option Nat)
    (g : Global) (args : Array Value)
    (_hsrc_ex : ∃ dt c, decls.getByKey g = some (.constructor dt c))
    (_hconc_ex : ∃ dt c, concDecls.getByKey g = some (.constructor dt c))
    (_ih : ∀ v ∈ args,
      flattenValue decls funcIdx v = Concrete.flattenValue concDecls funcIdx v)
    -- Hoisted ctor-shape agreement (sig amendment 2026-05-05): ctor-index
    -- agreement + dataType flat-size agreement, packaged as a single
    -- forall-quantified premise over the destructured pairs. Discharged
    -- downstream by composing `concretizeBuild_preserves_ctor_kind_at_entry_fwd`
    -- (Phase4.lean) + `step4Lower_constructor_explicit` (Shapes.lean) for the
    -- ctor-index half, and `dataTypeFlatSize_eq_layoutMap_size_wf` (Layout.lean,
    -- closed modulo bound-saturation) for the flat-size half.
    (_hCtorAgrees : ∀ {dt_src c_src dt_conc c_conc},
      decls.getByKey g = some (.constructor dt_src c_src) →
      concDecls.getByKey g = some (.constructor dt_conc c_conc) →
      (dt_src.constructors.findIdx? (· == c_src) |>.getD 0) =
        (dt_conc.constructors.findIdx? (· == c_conc) |>.getD 0) ∧
      dataTypeFlatSize decls {} dt_src = Concrete.dataTypeFlatSize concDecls {} dt_conc) :
    flattenValue decls funcIdx (.ctor g args) =
      Concrete.flattenValue concDecls funcIdx (.ctor g args) := by
  -- Reachability keepalives — primitives feed the discharge of `_hCtorAgrees`
  -- at the consumer site.
  let _ := @concretizeBuild_preserves_ctor_kind_at_entry_fwd
  let _ := @dataTypeFlatSize_eq_layoutMap_size_wf
  let _ := @layoutMap_dataType_size_extract
  -- Destructure both existence witnesses to expose the structured arm on each
  -- side of `flattenValue` / `Concrete.flattenValue`.
  obtain ⟨dt_src, c_src, hsrc⟩ := _hsrc_ex
  obtain ⟨dt_conc, c_conc, hconc⟩ := _hconc_ex
  obtain ⟨hidx, hsize⟩ := _hCtorAgrees hsrc hconc
  -- Unfold both sides: the `.ctor g args` arm dispatches on
  -- `decls.getByKey g` (source) and `concDecls.getByKey g` (concrete).
  unfold flattenValue Concrete.flattenValue
  rw [hsrc, hconc]
  -- Per-arg flatten agreement via `_ih`. The two `args.attach.flatMap`
  -- expressions agree pointwise.
  have hargsFlat :
      args.attach.flatMap (fun ⟨v, _⟩ => flattenValue decls funcIdx v) =
        args.attach.flatMap
          (fun ⟨v, _⟩ => Concrete.flattenValue concDecls funcIdx v) :=
    flatten_attach_flatMap_eq_pw _ih
  -- Combine: ctorIndex agreement (from `hidx`), per-arg flatten agreement
  -- (from `hargsFlat`), and dataType-flat-size agreement (from `hsize`)
  -- collapse the structured arms to identical arrays.
  simp only [hidx, hargsFlat, hsize]

/-- **Wire B bridge.** Entry-restricted variant of `flatten_agree_under_fullymono`.
Holds for `Value.FnFree v ∧ Value.MonoCtorReach decls concDecls v` values
(sig amended 2026-05-03 — see Invariant 3).

Closure status (F=0/F=1 by `Value` arm):
- `.unit/.field/.pointer` (F=0): direct unfold + rfl.
- `.fn` excluded by `FnFree` (F=0): inversion on `hFn`.
- `.tuple/.array` (F=0): pointwise + per-element IH (uses
  `MonoCtorReach.tuple_inv` / `_inv` to thread the predicate).
- `.ctor` (F=1, residual): delegated to `flatten_agree_entry_ctor_bridge`.
  `MonoCtorReach.ctor_src` / `_conc` discharge the structural-arm dispatch
  on both sides; the residual obligation is ctorIndex + dataTypeFlatSize
  agreement (see the bridge's docstring).

**Wider impact (2026-05-02)**: Closing `flatten_agree_entry_ctor_bridge`
also closes the `.ctor` arm of `Simulation.ValueR_of_FnFree_at_entry`
automatically — the latter consumes a `flatten_agree` witness as an
explicit parameter (now also amended to take `MonoCtorReach`), and the
use site in `Toplevel.compile_preservation_entry` supplies it from this
very theorem. So the two formerly duplicate `.ctor`-arm sorries
(B.3-shifted + A.5) collapsed into a single obligation living in the
sub-bridge above. -/
private theorem flatten_agree_entry
    {t : Source.Toplevel} {decls : Source.Decls}
    {typedDecls : Typed.Decls} {concDecls : Concrete.Decls}
    (_hdecls : t.mkDecls = .ok decls)
    (_hts : t.checkAndSimplify = .ok typedDecls)
    (_hconc : typedDecls.concretize = .ok concDecls)
    (_hwf : WellFormed t)
    (_hentry : HasEntryFn decls)
    (funcIdx : Global → Option Nat)
    -- Sig amendment 2026-05-05: hoist the per-key ctor-shape agreement
    -- (ctor-index + dataType flat-size) used by the `.ctor` arm. Threaded
    -- verbatim into `flatten_agree_entry_ctor_bridge`. Discharged at the
    -- top-level consumer (`Toplevel.compile_preservation_entry`) by composing
    -- `concretizeBuild_preserves_ctor_kind_at_entry_fwd` (Phase4.lean) +
    -- `step4Lower_constructor_explicit` (Shapes.lean) for the index half and
    -- `dataTypeFlatSize_eq_layoutMap_size_wf` (Layout.lean) for the size half.
    (_hCtorAgreesAll : ∀ (g : Global) {dt_src c_src dt_conc c_conc},
      decls.getByKey g = some (.constructor dt_src c_src) →
      concDecls.getByKey g = some (.constructor dt_conc c_conc) →
      (dt_src.constructors.findIdx? (· == c_src) |>.getD 0) =
        (dt_conc.constructors.findIdx? (· == c_conc) |>.getD 0) ∧
      dataTypeFlatSize decls {} dt_src = Concrete.dataTypeFlatSize concDecls {} dt_conc) :
    -- Sig amendment 2026-05-03 (Invariant 3): added `MonoCtorReach` premise.
    -- The `Value.FnFree`-only sig was provably False (counterexample at
    -- ctor names disagreeing across decls, see prior BLOCKED note version
    -- in this file's history). `MonoCtorReach decls concDecls v` pins every
    -- `.ctor g _` reachable in `v` to a global `g` keyed `.constructor` in
    -- BOTH decls, which is exactly what the structured `.ctor` arm needs.
    -- Discharged downstream by `runFunction_preserves_MonoCtorReach`
    -- (ValueEqFlatten.lean) at the `compile_preservation_entry` call site.
    ∀ (v : Value), Value.FnFree v → Value.MonoCtorReach decls concDecls v →
      flattenValue decls funcIdx v = Concrete.flattenValue concDecls funcIdx v
  | .unit, _, _ => by unfold flattenValue Concrete.flattenValue; rfl
  | .field _, _, _ => by unfold flattenValue Concrete.flattenValue; rfl
  | .pointer _ _, _, _ => by unfold flattenValue Concrete.flattenValue; rfl
  | .fn _, h, _ => nomatch h
  | .tuple vs, .tuple hfn, hreach => by
      unfold flattenValue Concrete.flattenValue
      have hreach_inv := hreach.tuple_inv
      have ih : ∀ v ∈ vs,
          flattenValue decls funcIdx v = Concrete.flattenValue concDecls funcIdx v :=
        fun v hv => flatten_agree_entry _hdecls _hts _hconc _hwf _hentry funcIdx
          _hCtorAgreesAll v (hfn v hv) (hreach_inv v hv)
      congr 1
      funext ⟨x, hx⟩
      exact ih x hx
  | .array vs, .array hfn, hreach => by
      unfold flattenValue Concrete.flattenValue
      have hreach_inv := hreach.array_inv
      have ih : ∀ v ∈ vs,
          flattenValue decls funcIdx v = Concrete.flattenValue concDecls funcIdx v :=
        fun v hv => flatten_agree_entry _hdecls _hts _hconc _hwf _hentry funcIdx
          _hCtorAgreesAll v (hfn v hv) (hreach_inv v hv)
      congr 1
      funext ⟨x, hx⟩
      exact ih x hx
  | .ctor g args, .ctor _ hfn, hreach => by
      -- Strengthened sig closes (i)/(ii)/(iii) of the original BLOCKED note:
      -- `MonoCtorReach.ctor_src` + `_conc` give us source-keyed AND
      -- concrete-keyed `.constructor` shapes at `g`. Both sides of the
      -- flatten now hit the *structured* arm with the same key `g`. What
      -- remains (case (iv)) is the genuine ctor-shape bridge:
      --   (A) ctorIndex agreement (same position in `dt.constructors`),
      --   (B) `dataTypeFlatSize` agreement, and
      --   (C) per-arg flatten via IH (already F=0 with `MonoCtorReach.ctor_args`).
      -- (A)/(B) live in `Aiur.flatten_agree_entry_ctor_bridge` below.
      -- Sig amendment 2026-05-04 (Defect 2): `MonoCtorReach.ctor`'s `hsrc`
      -- field now carries `dt.params = []`; weaken to the bridge's existing
      -- shape by dropping the params-empty conjunct. (Discharging Defect 2
      -- propagation only requires the dt/c witness here; the bridge body
      -- doesn't yet consume params-empty.)
      have hsrc_ex_full := hreach.ctor_src
      have hsrc_ex : ∃ dt c, decls.getByKey g = some (.constructor dt c) := by
        obtain ⟨dt, c, hg, _hpe⟩ := hsrc_ex_full
        exact ⟨dt, c, hg⟩
      have hconc_ex := hreach.ctor_conc
      have hreach_args := hreach.ctor_args
      have ih : ∀ v ∈ args,
          flattenValue decls funcIdx v = Concrete.flattenValue concDecls funcIdx v :=
        fun v hv => flatten_agree_entry _hdecls _hts _hconc _hwf _hentry funcIdx
          _hCtorAgreesAll v (hfn v hv) (hreach_args v hv)
      exact flatten_agree_entry_ctor_bridge _hdecls _hts _hconc _hwf _hentry
        funcIdx g args hsrc_ex hconc_ex ih (_hCtorAgreesAll g)
termination_by v _ _ => sizeOf v

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
(the FullyMono predecessor was DELETED 2026-04-28). Body is direct: thread
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

WIRE B (2026-04-28): body now REALLY composes through the entry-bridge
variants (`namespace_preservation_entry`, `flatten_agree_entry`,
`compile_ok_implies_struct_compatible_entry`,
`Lower.compile_preservation_entry`) and through
`concretize_preserves_runFunction_entry` (which itself REALLY composes through
`Aiur.Simulation.concretize_runFunction_simulation` modulo two named bridges).
The remaining open obligations are the four entry-bridge stubs above plus
`concretize_preserves_runFunction_entry`'s own `FullyMono` consumption — the
latter is upstream of this rewrite. -/
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
      -- Caller-provided: entry args satisfy `MonoCtorReach` against any
      -- concretized decls. For first-order entry args (Aiur invariant via
      -- `notPolyEntry`), this is trivially true (no `.ctor` reachable).
      -- Sig amendment 2026-05-03 (Invariant 3) — paired with
      -- `flatten_agree_entry`'s strengthened sig.
      (_hargsReach : ∀ (concDecls : Concrete.Decls),
        t.checkAndSimplify.toOption.bind (·.concretize.toOption) = some concDecls →
        ∀ v ∈ args, Value.MonoCtorReach decls concDecls v)
      -- Caller-provided: concrete returns are FnFree on the specific entry
      -- (type-soundness consequence of FO-return + RefClosed + TermRefsDt).
      (_hconcRetFnFree : ∀ (concDecls : Concrete.Decls) v io,
        t.checkAndSimplify.toOption.bind (·.concretize.toOption) = some concDecls →
        Concrete.Eval.runFunction concDecls (Global.mk name) args io₀ fuel = .ok (v, io) →
          Value.FnFree v)
      -- Caller-provided: concrete returns satisfy `MonoCtorReach`. Sig
      -- amendment 2026-05-03 — parallel of `_hconcRetFnFree`. Discharged by
      -- a Concrete-side mirror of `runFunction_preserves_MonoCtorReach`
      -- (parallel of the existing `Concrete.Eval.runFunction_preserves_FnFree`
      -- in ConcretizeSound/FnFree.lean) once the predicate-twin lemma is
      -- closed (currently BLOCKED-runFunction-preserves-MonoCtorReach).
      (_hconcRetReach : ∀ (concDecls : Concrete.Decls) v io,
        t.checkAndSimplify.toOption.bind (·.concretize.toOption) = some concDecls →
        Concrete.Eval.runFunction concDecls (Global.mk name) args io₀ fuel = .ok (v, io) →
          Value.MonoCtorReach decls concDecls v)
      -- Caller-provided: concretize produces nameAgrees structurally.
      (_hcdNameAgrees : ∀ (concDecls : Concrete.Decls),
        t.checkAndSimplify.toOption.bind (·.concretize.toOption) = some concDecls →
        ∀ (key : Global) (g : Concrete.Function),
          (key, Concrete.Declaration.function g) ∈ concDecls.pairs.toList → key = g.name)
      -- Caller-provided: simulation `Decls.R` (CtorPreserved + FnNamesAgree).
      -- Sig amendment 2026-05-03 (Defect 1) — replaces the placeholder
      -- `True` previously consumed by `step_R_preservation_applyGlobal`.
      (_hDeclsR : ∀ (concDecls : Concrete.Decls),
        t.checkAndSimplify.toOption.bind (·.concretize.toOption) = some concDecls →
        Aiur.Simulation.Decls.R decls concDecls)
      -- Caller-provided: per-key ctor-shape agreement (ctor-index +
      -- dataType-flat-size agreement). Sig amendment 2026-05-05 — paired
      -- with `flatten_agree_entry`'s strengthened sig (#13 closure). Discharged
      -- at the top-level `compile_correct` consumer by composing
      -- `concretizeBuild_preserves_ctor_kind_at_entry_fwd` + `step4Lower_constructor_explicit`
      -- (ctor-index half) and `dataTypeFlatSize_eq_layoutMap_size_wf`
      -- (flat-size half).
      (_hCtorAgreesAll : ∀ (concDecls : Concrete.Decls),
        t.checkAndSimplify.toOption.bind (·.concretize.toOption) = some concDecls →
        ∀ (g : Global) {dt_src c_src dt_conc c_conc},
          decls.getByKey g = some (.constructor dt_src c_src) →
          concDecls.getByKey g = some (.constructor dt_conc c_conc) →
          (dt_src.constructors.findIdx? (· == c_src) |>.getD 0) =
            (dt_conc.constructors.findIdx? (· == c_conc) |>.getD 0) ∧
          dataTypeFlatSize decls {} dt_src =
            Concrete.dataTypeFlatSize concDecls {} dt_conc),
      InterpResultEq decls ct.globalFuncIdx retTyp
        (Source.Eval.runFunction decls (Global.mk name) args io₀ fuel)
        (Bytecode.Eval.runFunction ct.bytecode funIdx
          (Flatten.args decls ct.globalFuncIdx args) io₀ fuel) := by
  intros name funIdx hname f hsrc hentry args io₀ fuel retTyp hargsFnFree
         hargsReach hconcRetFnFree hconcRetReach hcdNameAgrees hDeclsR hCtorAgreesAll
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
    -- (5a) Build the flatten-agreement witness via `flatten_agree_entry`.
    -- We hoist this BEFORE the Wire A call so the same witness can be threaded
    -- through `concretize_preserves_runFunction_entry` (which now consumes it
    -- to discharge the `.ctor` arm of `Simulation.ValueR_of_FnFree_at_entry`).
    -- Sig amendment 2026-05-03: `hflatten_agree` now also takes
    -- `MonoCtorReach v` (mirroring `flatten_agree_entry`'s strengthened sig).
    -- Sig amendment 2026-05-05: `flatten_agree_entry` now takes a hoisted
    -- `_hCtorAgreesAll` premise (per-key ctor-index + dataType-flat-size
    -- agreement). Discharged at the top-level `compile_correct` consumer
    -- by composing the closed Phase4 / Shapes / Layout primitives there.
    have hflatten_agree :=
      flatten_agree_entry hdecls hts hconc hwf hHasEntry ct.globalFuncIdx
        (hCtorAgreesAll concDecls hToOptionPre)
    -- Args MonoCtorReach derived from caller hypothesis at this concretization.
    have hargsReachConc : ∀ v ∈ args, Value.MonoCtorReach decls concDecls v :=
      hargsReach concDecls hToOptionPre
    -- Caller-provided `Decls.R decls concDecls` (sig amendment 2026-05-03,
    -- Defect 1) — the bundled simulation precondition required by
    -- `step_R_preservation_applyGlobal`. Discharged at the top-level
    -- `compile_correct` call site by composing
    -- `concretizeBuild_preserves_{function,ctor}_kind_at_entry_fwd` +
    -- the `step4Lower_backward_*` family.
    have hDeclsR_inst : Aiur.Simulation.Decls.R decls concDecls :=
      hDeclsR concDecls hToOptionPre
    -- (4) Apply Wire A: produces `Concrete.flattenValue concDecls` on RHS.
    have h_a_raw := concretize_preserves_runFunction_entry
      (Global.mk name) f f_conc hsrc hconcF hentry h_inputs_match
      args io₀ fuel ct.globalFuncIdx hargsFnFree hargsReachConc hDeclsR_inst
      hflatten_agree
    -- (5b) Bridge: convert `Concrete.flattenValue concDecls _ v₂` to
    -- `flattenValue decls _ v₂` via `hflatten_agree` (FnFree side).
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
          -- Bridge `Concrete.flattenValue v₂` ↦ `flattenValue v₂` via
          -- `hflatten_agree v₂`. The bridge needs `Value.FnFree v₂` and
          -- `Value.MonoCtorReach _ _ v₂`. Both come from caller-provided
          -- type-soundness witnesses on the concrete return.
          have hv₂_fnfree : Value.FnFree v₂ :=
            hconcRetFnFree concDecls v₂ io₂ hToOptionPre hconcRun
          have hv₂_reach : Value.MonoCtorReach decls concDecls v₂ :=
            hconcRetReach concDecls v₂ io₂ hToOptionPre hconcRun
          rw [hflat]; exact (hflatten_agree v₂ hv₂_fnfree hv₂_reach).symm
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
