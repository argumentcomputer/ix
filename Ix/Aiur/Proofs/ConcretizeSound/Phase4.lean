module
public import Ix.Aiur.Proofs.ConcretizeSound
public import Ix.Aiur.Proofs.ConcretizeSound.CtorKind

/-!
Phase A.4 (full source↔concrete ctor kind correspondence) + Phase B
prerequisites + Wire B (entry-restricted concretize ctor-present
propagation). Extracted from `ConcretizeSound.lean` 2026-04-29.
-/

public section

namespace Aiur

open Source

/-! ### PLAN_3B Phase A.4 — full source↔concrete ctor kind correspondence.

End-to-end composition of A.1 (source↔typed) + A.2 (typed↔mono) + A.3
(mono↔concrete). Disjointness conditions for A.2 derived from FullyMono +
IndexMap key uniqueness via `concretize_drain_preserves_StrongNewNameShape`. -/

theorem concretize_under_fullymono_preserves_ctor_kind_fwd
    {t : Source.Toplevel} {decls : Source.Decls}
    {typedDecls : Typed.Decls} {concDecls : Concrete.Decls}
    (hmono : FullyMonomorphic t)
    (hdecls : t.mkDecls = .ok decls)
    (hts : t.checkAndSimplify = .ok typedDecls)
    (hconc : typedDecls.concretize = .ok concDecls)
    {g : Global} {dt : DataType} {c : Constructor}
    (hsrc : decls.getByKey g = some (.constructor dt c)) :
    ∃ cdt cd_c, concDecls.getByKey g = some (.constructor cdt cd_c) := by
  -- A.1: source → typed.
  obtain ⟨td_dt, td_c, htd⟩ := checkAndSimplify_preserves_ctor_kind_fwd hdecls hts hsrc
  -- FnMatchP backward: typed ctor at g equals source ctor at g (same dt+c).
  have hP := FnMatchP_checkAndSimplify hdecls hts
  have hsrc_again : decls.getByKey g = some (.constructor td_dt td_c) :=
    (hP g).2.2 td_dt td_c htd
  rw [hsrc] at hsrc_again
  cases hsrc_again
  -- Now `htd : typedDecls.getByKey g = some (.constructor dt c)` (via Option.some
  -- + ctor injection in `cases`).
  -- Source dt at dt.name (via mkDecls_ctor_companion).
  obtain ⟨hsrc_dt, _hcmem⟩ := mkDecls_ctor_companion hdecls g dt c hsrc
  -- Under FullyMono, source dt has params = [].
  have hsrcMonoP := SrcDtParamsMonoP_mkDecls hmono hdecls
  have hdt_params : dt.params = [] := hsrcMonoP dt.name dt hsrc_dt
  -- Extract drained + monoDecls from hconc.
  unfold Typed.Decls.concretize at hconc
  simp only [bind, Except.bind] at hconc
  split at hconc
  · cases hconc
  rename_i drained hdrain
  -- Params-empty for typed decls (FullyMono).
  have hfn_params_empty : ∀ k f, typedDecls.getByKey k = some (.function f) → f.params = [] :=
    typedDecls_params_empty_of_fullyMonomorphic hmono hdecls hts
  have hdt_params_empty : ∀ k dt', typedDecls.getByKey k = some (.dataType dt') → dt'.params = [] :=
    typedDecls_dt_params_empty_of_fullyMonomorphic hmono hdecls hts
  -- StrongNewNameShape preserved through drain.
  have hSNN := concretize_drain_preserves_StrongNewNameShape _ _
    (DrainState.StrongNewNameShape.init typedDecls (concretizeSeed typedDecls)) hdrain
  -- Disjointness for newDataTypes.
  have hDtNotKey : ∀ newDt ∈ drained.newDataTypes, newDt.name ≠ g := by
    intro newDt hmem heq
    obtain ⟨g_orig, args, dt_orig, hname, hget_orig, hargs_sz, _⟩ := hSNN.2 newDt hmem
    have hdt_orig_params := hdt_params_empty g_orig dt_orig hget_orig
    have hargs_zero : args.size = 0 := by rw [hargs_sz, hdt_orig_params]; rfl
    have hargs_empty : args = #[] := Array.size_eq_zero_iff.mp hargs_zero
    have hname_eq : newDt.name = g_orig := by
      rw [hname, hargs_empty]; exact concretizeName_empty_args g_orig
    rw [hname_eq] at heq
    -- heq : g_orig = g; hget_orig : tds.getByKey g_orig = .dataType _;
    -- htd : tds.getByKey g = .constructor _ _; contradiction via IndexMap uniqueness.
    rw [heq] at hget_orig
    rw [htd] at hget_orig
    cases hget_orig
  -- Disjointness for newFunctions.
  have hFnNotKey : ∀ newFn ∈ drained.newFunctions, newFn.name ≠ g := by
    intro newFn hmem heq
    obtain ⟨g_orig, args, f_orig, hname, hget_orig, hargs_sz⟩ := hSNN.1 newFn hmem
    have hf_orig_params := hfn_params_empty g_orig f_orig hget_orig
    have hargs_zero : args.size = 0 := by rw [hargs_sz, hf_orig_params]; rfl
    have hargs_empty : args = #[] := Array.size_eq_zero_iff.mp hargs_zero
    have hname_eq : newFn.name = g_orig := by
      rw [hname, hargs_empty]; exact concretizeName_empty_args g_orig
    rw [hname_eq] at heq
    rw [heq] at hget_orig
    rw [htd] at hget_orig
    cases hget_orig
  -- A.2: typed → mono.
  obtain ⟨md_dt, md_c, hmono_get⟩ :=
    PhaseA2.concretizeBuild_preserves_ctor_kind_fwd typedDecls drained.mono
      drained.newFunctions drained.newDataTypes htd hdt_params hDtNotKey hFnNotKey
  -- A.3: mono → concrete.
  exact step4Lower_preserves_ctor_kind_fwd hmono_get hconc

/-- Phase A.4 dataType analog: under `FullyMonomorphic`, source `.dataType`
at `g` propagates to concrete `.dataType` at `g`. Mirrors
`concretize_under_fullymono_preserves_ctor_kind_fwd`. -/
theorem concretize_under_fullymono_preserves_dataType_kind_fwd
    {t : Source.Toplevel} {decls : Source.Decls}
    {typedDecls : Typed.Decls} {concDecls : Concrete.Decls}
    (hmono : FullyMonomorphic t)
    (hdecls : t.mkDecls = .ok decls)
    (hts : t.checkAndSimplify = .ok typedDecls)
    (hconc : typedDecls.concretize = .ok concDecls)
    {g : Global} {dt : DataType}
    (hsrc : decls.getByKey g = some (.dataType dt)) :
    ∃ cdt, concDecls.getByKey g = some (.dataType cdt) := by
  -- A.1: source → typed.
  obtain ⟨td_dt, htd⟩ := checkAndSimplify_src_dt_to_td hdecls hts hsrc
  -- Under FullyMono, typed dt has params = [].
  have hdt_params_empty : ∀ k dt', typedDecls.getByKey k = some (.dataType dt') →
      dt'.params = [] := typedDecls_dt_params_empty_of_fullyMonomorphic hmono hdecls hts
  have hdt_params : td_dt.params = [] := hdt_params_empty g td_dt htd
  -- Extract drained from hconc.
  unfold Typed.Decls.concretize at hconc
  simp only [bind, Except.bind] at hconc
  split at hconc
  · cases hconc
  rename_i drained hdrain
  have hfn_params_empty : ∀ k f, typedDecls.getByKey k = some (.function f) → f.params = [] :=
    typedDecls_params_empty_of_fullyMonomorphic hmono hdecls hts
  -- StrongNewNameShape preserved through drain.
  have hSNN := concretize_drain_preserves_StrongNewNameShape _ _
    (DrainState.StrongNewNameShape.init typedDecls (concretizeSeed typedDecls)) hdrain
  -- Disjointness: no inner ctor key in any drained.newDataTypes equals g.
  have hDtCtorNotKey : ∀ newDt ∈ drained.newDataTypes,
      ∀ c ∈ newDt.constructors,
        newDt.name.pushNamespace c.nameHead ≠ g := by
    intro newDt hmem c hc heq
    obtain ⟨g_orig, args, dt_orig, hname, hget_orig, hargs_sz, hctors⟩ := hSNN.2 newDt hmem
    have hdt_orig_params := hdt_params_empty g_orig dt_orig hget_orig
    have hargs_zero : args.size = 0 := by rw [hargs_sz, hdt_orig_params]; rfl
    have hargs_empty : args = #[] := Array.size_eq_zero_iff.mp hargs_zero
    have hname_eq : newDt.name = g_orig := by
      rw [hname, hargs_empty]; exact concretizeName_empty_args g_orig
    -- c.nameHead matches some c_orig.nameHead in dt_orig.
    have hmem_map : c.nameHead ∈ newDt.constructors.map (·.nameHead) :=
      List.mem_map_of_mem hc
    rw [hctors, List.mem_map] at hmem_map
    obtain ⟨c_orig, hc_orig_mem, hc_orig_nameHead⟩ := hmem_map
    -- Source dt at g_orig (typed dt_orig — by FnMatchP backward).
    have hP := FnMatchP_checkAndSimplify hdecls hts
    have hsrc_dt : decls.getByKey g_orig = some (.dataType dt_orig) :=
      (hP g_orig).2.1 dt_orig hget_orig
    -- mkDecls_dt_implies_ctor_keys: source has .ctor at g_orig.pushNamespace c_orig.nameHead.
    have hsrc_ctor :=
      mkDecls_dt_implies_ctor_keys hdecls g_orig dt_orig hsrc_dt c_orig hc_orig_mem
    -- newDt.name.pushNamespace c.nameHead = g_orig.pushNamespace c_orig.nameHead.
    rw [hname_eq, ← hc_orig_nameHead] at heq
    -- heq: g_orig.pushNamespace c_orig.nameHead = g.
    rw [heq] at hsrc_ctor
    -- hsrc_ctor : decls.getByKey g = some (.constructor dt_orig c_orig);
    -- hsrc      : decls.getByKey g = some (.dataType dt); contradiction.
    rw [hsrc] at hsrc_ctor
    cases hsrc_ctor
  -- Disjointness for newFunctions.
  have hFnNotKey : ∀ newFn ∈ drained.newFunctions, newFn.name ≠ g := by
    intro newFn hmem heq
    obtain ⟨g_orig, args, f_orig, hname, hget_orig, hargs_sz⟩ := hSNN.1 newFn hmem
    have hf_orig_params := hfn_params_empty g_orig f_orig hget_orig
    have hargs_zero : args.size = 0 := by rw [hargs_sz, hf_orig_params]; rfl
    have hargs_empty : args = #[] := Array.size_eq_zero_iff.mp hargs_zero
    have hname_eq : newFn.name = g_orig := by
      rw [hname, hargs_empty]; exact concretizeName_empty_args g_orig
    rw [hname_eq] at heq
    rw [heq] at hget_orig
    rw [htd] at hget_orig
    cases hget_orig
  -- A.2: typed → mono.
  obtain ⟨md_dt, hmono_get⟩ :=
    PhaseA2.concretizeBuild_preserves_dataType_kind_fwd typedDecls drained.mono
      drained.newFunctions drained.newDataTypes htd hdt_params hDtCtorNotKey hFnNotKey
  -- A.3: mono → concrete.
  exact step4Lower_preserves_dataType_kind_fwd hmono_get hconc

/-! #### Entry-restricted variant under `WellFormed`. -/

/-- Under `Typed.Decls.ConcretizeUniqueNames` (carried by `WellFormed.noNameCollisions`),
typed `.function tf` at `name` with `tf.params = []` propagates to `monoDecls`
(= `concretizeBuild` output) carrying `.function` at the same key.

Closure path: trace through the three folds of `concretizeBuild`.
* **srcStep-fold** at `(name, .function tf)` with `tf.params.isEmpty = true`
  inserts `.function` at `name` (via `fromSource_inserts_function_at_key`);
  other source pairs at different keys preserve via `srcStep_foldl_no_g_preserves`.
* **dtStep-fold** could overwrite at `name` only if `dt.name = name` or
  `dt.name.pushNamespace c.nameHead = name` for some `dt ∈ drained.newDataTypes`.
  Both ruled out via `concretize_drain_preserves_StrongNewNameShape` +
  `ConcretizeUniqueNames`:
  - `dt.name = name` case: StrongNewNameShape ⟹ `dt.name = concretizeName g_orig args`
    for typed `.dataType` at `g_orig`. With witness from `concDecls.getByKey name
    = some _`, uniqueness forces `g_orig = name ∧ args = #[]`, but typed has
    `.function` at `name` (not `.dataType`), contradiction.
  - inner-ctor case: similar, with witness from `concDecls.containsKey
    dt.name` (via `concretizeBuild_containsKey_newDt_name` +
    `concretize_step_4_keys_of_fold` lifting), uniqueness forces `args = #[]`
    so `dt.name = g_orig`. Then `g_orig.pushNamespace c_orig.nameHead = name`
    (via StrongNewNameShape's ctors-nameHead correspondence), and source
    `mkDecls_dt_implies_ctor_keys` puts a `.constructor` at `name`,
    contradicting source `.function` at `name` (lifted from typed via
    `FnMatchP_checkAndSimplify`).
* **fnStep-fold** preserves `.function` kind unconditionally. -/
theorem concretizeBuild_preserves_function_kind_at_entry_fwd
    {t : Source.Toplevel} {decls : Source.Decls}
    {typedDecls : Typed.Decls} {concDecls : Concrete.Decls}
    {drained : DrainState}
    (hdecls : t.mkDecls = .ok decls)
    (hts : t.checkAndSimplify = .ok typedDecls)
    (hdrain : concretizeDrain typedDecls (concretizeDrainFuel typedDecls)
      { pending := concretizeSeed typedDecls, seen := {}, mono := {},
        newFunctions := #[], newDataTypes := #[] } = .ok drained)
    (hconc : typedDecls.concretize = .ok concDecls)
    (hUniqueNames : Typed.Decls.ConcretizeUniqueNames typedDecls)
    {name : Global} {tf : Typed.Function}
    (htyped : typedDecls.getByKey name = some (.function tf))
    (htf_params : tf.params = []) :
    ∃ md_f, (concretizeBuild typedDecls drained.mono drained.newFunctions
      drained.newDataTypes).getByKey name = some (.function md_f) := by
  -- StrongNewNameShape preserved through drain.
  have hSNN := concretize_drain_preserves_StrongNewNameShape _ _
    (DrainState.StrongNewNameShape.init typedDecls (concretizeSeed typedDecls)) hdrain
  -- Witness for noNameCollisions: derived FORWARD via insert-only properties of
  -- the three folds + step4Lower keys-iff. srcStep at `(name, .function tf)`
  -- with `tf.params = []` inserts at `name`; dtStep/fnStep folds preserve via
  -- containsKey monotonicity; step4Lower keys-iff lifts to concDecls.
  have hWit : ∃ d, concDecls.getByKey name = some d := by
    have hSrc := PhaseA2.fromSource_inserts_function_at_key typedDecls drained.mono
      htyped htf_params
    obtain ⟨_, hSrcGet⟩ := hSrc
    have hSrcContains :
        (typedDecls.pairs.foldl (PhaseA2.srcStep typedDecls drained.mono) default).containsKey
          name :=
      (IndexMap.getByKey_isSome_iff_containsKey _ _).mp (by rw [hSrcGet]; rfl)
    have hDtContains :
        (drained.newDataTypes.foldl (PhaseA2.dtStep drained.mono)
          (typedDecls.pairs.foldl (PhaseA2.srcStep typedDecls drained.mono) default)).containsKey
          name :=
      PhaseA2.dtStep_foldl_preserves_containsKey drained.mono drained.newDataTypes _ hSrcContains
    have hBuildContains : (concretizeBuild typedDecls drained.mono drained.newFunctions
        drained.newDataTypes).containsKey name := by
      rw [PhaseA2.concretizeBuild_eq]
      exact PhaseA2.fnStep_foldl_preserves_containsKey typedDecls drained.mono
        drained.newFunctions _ hDtContains
    have hconc_unfold := hconc
    unfold Typed.Decls.concretize at hconc_unfold
    simp only [bind, Except.bind] at hconc_unfold
    rw [hdrain] at hconc_unfold
    have hkeys_iff := concretize_step_4_keys_of_fold step4Lower
      step4Lower_inserts hconc_unfold
    have hconc_contains : concDecls.containsKey name :=
      (hkeys_iff name).mp hBuildContains
    have hconc_get_ne : concDecls.getByKey name ≠ none := by
      rw [IndexMap.getByKey_ne_none_iff_containsKey]; exact hconc_contains
    cases hg : concDecls.getByKey name with
    | none => exact absurd hg hconc_get_ne
    | some d => exact ⟨d, rfl⟩
  -- name = concretizeName name #[].
  have hname_self : concretizeName name #[] = name := concretizeName_empty_args name
  -- Disjointness for newDataTypes (dt.name ≠ name).
  have hDtNotKey : ∀ newDt ∈ drained.newDataTypes, newDt.name ≠ name := by
    intro newDt hmem heq
    obtain ⟨g_orig, args, dt_orig, hname_eq, hget_orig, _hargs_sz, _⟩ := hSNN.2 newDt hmem
    -- newDt.name = concretizeName g_orig args = name. So concretizeName g_orig args = name.
    have hcn_eq : concretizeName g_orig args = name := by rw [← hname_eq]; exact heq
    -- name = concretizeName name #[]; so concretizeName g_orig args = concretizeName name #[].
    have hcn_eq2 : concretizeName g_orig args = concretizeName name #[] := by
      rw [hcn_eq]; exact hname_self.symm
    -- noNameCollisions: g_orig = name ∧ args = #[].
    have hWit' : ∃ d, concDecls.getByKey (concretizeName g_orig args) = some d := by
      rw [hcn_eq]; exact hWit
    obtain ⟨hg_eq, _⟩ := hUniqueNames hconc g_orig name args #[] hcn_eq2 hWit'
    -- typed has .dataType dt_orig at g_orig = name; but typed has .function tf at name. Contradiction.
    rw [hg_eq] at hget_orig
    rw [htyped] at hget_orig
    cases hget_orig
  -- Disjointness for newDataTypes inner-ctors (dt.name.pushNamespace c.nameHead ≠ name).
  -- Closure path: under the witness `concDecls.containsKey newDt.name` (derived
  -- from `concretizeBuild_containsKey_newDt_name` + `concretize_step_4_keys_of_fold`),
  -- `noNameCollisions` forces `args = #[]` on the StrongNewNameShape equation
  -- `newDt.name = concretizeName g_orig args`. Then `g_orig = newDt.name` (and
  -- `args = #[]` gives `concretizeName g_orig args = g_orig`, consistent).
  -- Combined with `c.nameHead = c_orig.nameHead`, we get
  -- `g_orig.pushNamespace c_orig.nameHead = name`, contradicting typed
  -- `.function tf` at `name` via `mkDecls_dt_implies_ctor_keys` + FnMatchP.
  have hDtCtorNotKey : ∀ newDt ∈ drained.newDataTypes,
      ∀ c ∈ newDt.constructors,
        newDt.name.pushNamespace c.nameHead ≠ name := by
    intro newDt hmem c hc heq
    -- StrongNewNameShape: newDt.name = concretizeName g_orig args, with typed
    -- `.dataType dt_orig` at `g_orig`, and ctor-nameHeads matching `dt_orig`.
    obtain ⟨g_orig, args, dt_orig, hname_eq, hget_orig, _hargs_sz, hctors_map⟩ :=
      hSNN.2 newDt hmem
    -- Witness: monoDecls (= concretizeBuild output) contains key newDt.name.
    have hmono_contains : (concretizeBuild typedDecls drained.mono drained.newFunctions
        drained.newDataTypes).containsKey newDt.name :=
      PhaseA2.concretizeBuild_containsKey_newDt_name typedDecls drained.mono
        drained.newFunctions drained.newDataTypes hmem
    -- Lift to concDecls via step 4 fold.
    have hconc_unfold := hconc
    unfold Typed.Decls.concretize at hconc_unfold
    simp only [bind, Except.bind] at hconc_unfold
    rw [hdrain] at hconc_unfold
    -- `hconc_unfold : (concretizeBuild ...).foldlM step4Lower (init := default) = .ok concDecls`.
    have hkeys_iff := concretize_step_4_keys_of_fold step4Lower
      step4Lower_inserts hconc_unfold
    have hconc_contains : concDecls.containsKey newDt.name :=
      (hkeys_iff newDt.name).mp hmono_contains
    have hconc_get_ne : concDecls.getByKey newDt.name ≠ none := by
      rw [IndexMap.getByKey_ne_none_iff_containsKey]; exact hconc_contains
    have hconc_get_some : ∃ d, concDecls.getByKey newDt.name = some d := by
      cases hg : concDecls.getByKey newDt.name with
      | none => exact absurd hg hconc_get_ne
      | some d => exact ⟨d, rfl⟩
    -- Now apply noNameCollisions on `concretizeName g_orig args = concretizeName newDt.name #[]`.
    have hcn_self_dt : concretizeName newDt.name #[] = newDt.name :=
      concretizeName_empty_args newDt.name
    have hcn_eq2 : concretizeName g_orig args = concretizeName newDt.name #[] := by
      rw [hcn_self_dt, ← hname_eq]
    have hWit_dt : ∃ d, concDecls.getByKey (concretizeName g_orig args) = some d := by
      rw [← hname_eq]; exact hconc_get_some
    obtain ⟨hg_eq, hargs_eq⟩ :=
      hUniqueNames hconc g_orig newDt.name args #[] hcn_eq2 hWit_dt
    -- `args = #[]` ⟹ `concretizeName g_orig args = g_orig`. So `newDt.name = g_orig`.
    have hcn_g : concretizeName g_orig args = g_orig := by
      rw [hargs_eq]; exact concretizeName_empty_args g_orig
    have hdt_name_g : newDt.name = g_orig := by rw [hname_eq]; exact hcn_g
    -- `c.nameHead = c_orig.nameHead` for some `c_orig ∈ dt_orig.constructors`.
    have hc_nh_mem : c.nameHead ∈ newDt.constructors.map (·.nameHead) :=
      List.mem_map_of_mem hc
    rw [hctors_map, List.mem_map] at hc_nh_mem
    obtain ⟨c_orig, hc_orig_mem, hc_orig_nh⟩ := hc_nh_mem
    -- Extract source-side decls (mkDecls = .ok decls).
    -- `mkDecls_dt_implies_ctor_keys` requires source `.dataType` at g_orig.
    -- Lift typed `.dataType dt_orig` at g_orig back to source via FnMatchP.
    have hP := FnMatchP_checkAndSimplify hdecls hts
    have hsrc_dt : decls.getByKey g_orig = some (.dataType dt_orig) :=
      (hP g_orig).2.1 dt_orig hget_orig
    -- Source has `.constructor dt_orig c_orig` at g_orig.pushNamespace c_orig.nameHead.
    have hsrc_ctor :=
      mkDecls_dt_implies_ctor_keys hdecls g_orig dt_orig hsrc_dt c_orig hc_orig_mem
    -- Now: dt.name.pushNamespace c.nameHead = name (heq); also dt.name = g_orig;
    -- and c_orig.nameHead = c.nameHead. So g_orig.pushNamespace c_orig.nameHead = name.
    rw [hdt_name_g, ← hc_orig_nh] at heq
    -- heq : g_orig.pushNamespace c_orig.nameHead = name. Source has .ctor at LHS.
    rw [heq] at hsrc_ctor
    -- hsrc_ctor : decls.getByKey name = some (.constructor dt_orig c_orig).
    -- By FnMatchP forward, typed `.function tf` at name (htyped) ⟹ source `.function f` at name.
    -- This contradicts hsrc_ctor (IndexMap key uniqueness).
    obtain ⟨f_src, hsrc_f, _⟩ := (hP name).1 tf htyped
    rw [hsrc_f] at hsrc_ctor
    cases hsrc_ctor
  -- Disjointness for newFunctions (vacuous: fnStep always inserts .function).
  -- Apply the 3-fold trace.
  rw [PhaseA2.concretizeBuild_eq]
  -- srcStep-fold puts .function at name.
  have h1 := PhaseA2.fromSource_inserts_function_at_key typedDecls drained.mono htyped htf_params
  -- dtStep-fold preserves: under hDtNotKey + hDtCtorNotKey, getByKey name unchanged.
  have h2 :
      (drained.newDataTypes.foldl (PhaseA2.dtStep drained.mono)
        (typedDecls.pairs.foldl (PhaseA2.srcStep typedDecls drained.mono) default)).getByKey name
      = (typedDecls.pairs.foldl (PhaseA2.srcStep typedDecls drained.mono) default).getByKey name := by
    rw [← Array.foldl_toList]
    apply PhaseA2.dtStep_foldl_no_g_preserves drained.mono drained.newDataTypes.toList _
    · intro dt hdt
      exact hDtNotKey dt (Array.mem_toList_iff.mp hdt)
    · intro dt hdt c hc
      exact hDtCtorNotKey dt (Array.mem_toList_iff.mp hdt) c hc
  -- fnStep-fold preserves .function kind.
  have h3 :
      ∃ md_f, (drained.newDataTypes.foldl (PhaseA2.dtStep drained.mono)
        (typedDecls.pairs.foldl (PhaseA2.srcStep typedDecls drained.mono) default)).getByKey name
        = some (.function md_f) := by
    rw [h2]; exact h1
  exact PhaseA2.fnStep_foldl_preserves_function_kind typedDecls drained.mono drained.newFunctions _ h3

/-- Strengthened entry-fwd: `concretizeBuild` carries an entry `.function md_f`
at `name` with `md_f.inputs.map (·.1) = tf.inputs.map (·.1)`. Same closure
path as `concretizeBuild_preserves_function_kind_at_entry_fwd` but uses
strengthened srcStep/fnStep helpers that carry the inputs-label invariant.
The fnStep step uses `NewFnInputsLabelShape` (a parallel drain invariant)
combined with `ConcretizeUniqueNames` + entry-seed identity to identify any
overwriting `f' ∈ newFunctions` at `name` as having inputs labels matching
`tf.inputs`. -/
theorem concretizeBuild_preserves_function_inputs_at_entry_fwd
    {t : Source.Toplevel} {decls : Source.Decls}
    {typedDecls : Typed.Decls} {concDecls : Concrete.Decls}
    {drained : DrainState}
    (hdecls : t.mkDecls = .ok decls)
    (hts : t.checkAndSimplify = .ok typedDecls)
    (hdrain : concretizeDrain typedDecls (concretizeDrainFuel typedDecls)
      { pending := concretizeSeed typedDecls, seen := {}, mono := {},
        newFunctions := #[], newDataTypes := #[] } = .ok drained)
    (hconc : typedDecls.concretize = .ok concDecls)
    (hUniqueNames : Typed.Decls.ConcretizeUniqueNames typedDecls)
    {name : Global} {tf : Typed.Function}
    (htyped : typedDecls.getByKey name = some (.function tf))
    (htf_params : tf.params = []) :
    ∃ md_f, (concretizeBuild typedDecls drained.mono drained.newFunctions
      drained.newDataTypes).getByKey name = some (.function md_f) ∧
      md_f.inputs.map (·.1) = tf.inputs.map (·.1) := by
  -- StrongNewNameShape preserved through drain.
  have hSNN := concretize_drain_preserves_StrongNewNameShape _ _
    (DrainState.StrongNewNameShape.init typedDecls (concretizeSeed typedDecls)) hdrain
  -- NewFnInputsLabelShape preserved through drain.
  have hNFI := concretize_drain_preserves_NewFnInputsLabelShape _ _
    (DrainState.NewFnInputsLabelShape.init typedDecls (concretizeSeed typedDecls)) hdrain
  -- Witness for noNameCollisions: derived FORWARD via insert-only properties of
  -- the three folds + step4Lower keys-iff (mirrors the kind-only variant above).
  have hWit : ∃ d, concDecls.getByKey name = some d := by
    have hSrc := PhaseA2.fromSource_inserts_function_at_key typedDecls drained.mono
      htyped htf_params
    obtain ⟨_, hSrcGet⟩ := hSrc
    have hSrcContains :
        (typedDecls.pairs.foldl (PhaseA2.srcStep typedDecls drained.mono) default).containsKey
          name :=
      (IndexMap.getByKey_isSome_iff_containsKey _ _).mp (by rw [hSrcGet]; rfl)
    have hDtContains :
        (drained.newDataTypes.foldl (PhaseA2.dtStep drained.mono)
          (typedDecls.pairs.foldl (PhaseA2.srcStep typedDecls drained.mono) default)).containsKey
          name :=
      PhaseA2.dtStep_foldl_preserves_containsKey drained.mono drained.newDataTypes _ hSrcContains
    have hBuildContains : (concretizeBuild typedDecls drained.mono drained.newFunctions
        drained.newDataTypes).containsKey name := by
      rw [PhaseA2.concretizeBuild_eq]
      exact PhaseA2.fnStep_foldl_preserves_containsKey typedDecls drained.mono
        drained.newFunctions _ hDtContains
    have hconc_unfold := hconc
    unfold Typed.Decls.concretize at hconc_unfold
    simp only [bind, Except.bind] at hconc_unfold
    rw [hdrain] at hconc_unfold
    have hkeys_iff := concretize_step_4_keys_of_fold step4Lower
      step4Lower_inserts hconc_unfold
    have hconc_contains : concDecls.containsKey name :=
      (hkeys_iff name).mp hBuildContains
    have hconc_get_ne : concDecls.getByKey name ≠ none := by
      rw [IndexMap.getByKey_ne_none_iff_containsKey]; exact hconc_contains
    cases hg : concDecls.getByKey name with
    | none => exact absurd hg hconc_get_ne
    | some d => exact ⟨d, rfl⟩
  -- name = concretizeName name #[].
  have hname_self : concretizeName name #[] = name := concretizeName_empty_args name
  -- Disjointness for newDataTypes (dt.name ≠ name).
  have hDtNotKey : ∀ newDt ∈ drained.newDataTypes, newDt.name ≠ name := by
    intro newDt hmem heq
    obtain ⟨g_orig, args, dt_orig, hname_eq, hget_orig, _hargs_sz, _⟩ := hSNN.2 newDt hmem
    have hcn_eq : concretizeName g_orig args = name := by rw [← hname_eq]; exact heq
    have hcn_eq2 : concretizeName g_orig args = concretizeName name #[] := by
      rw [hcn_eq]; exact hname_self.symm
    have hWit' : ∃ d, concDecls.getByKey (concretizeName g_orig args) = some d := by
      rw [hcn_eq]; exact hWit
    obtain ⟨hg_eq, _⟩ := hUniqueNames hconc g_orig name args #[] hcn_eq2 hWit'
    rw [hg_eq] at hget_orig
    rw [htyped] at hget_orig
    cases hget_orig
  -- Disjointness for newDataTypes inner-ctors.
  have hDtCtorNotKey : ∀ newDt ∈ drained.newDataTypes,
      ∀ c ∈ newDt.constructors,
        newDt.name.pushNamespace c.nameHead ≠ name := by
    intro newDt hmem c hc heq
    obtain ⟨g_orig, args, dt_orig, hname_eq, hget_orig, _hargs_sz, hctors_map⟩ :=
      hSNN.2 newDt hmem
    have hmono_contains : (concretizeBuild typedDecls drained.mono drained.newFunctions
        drained.newDataTypes).containsKey newDt.name :=
      PhaseA2.concretizeBuild_containsKey_newDt_name typedDecls drained.mono
        drained.newFunctions drained.newDataTypes hmem
    have hconc_unfold := hconc
    unfold Typed.Decls.concretize at hconc_unfold
    simp only [bind, Except.bind] at hconc_unfold
    rw [hdrain] at hconc_unfold
    have hkeys_iff := concretize_step_4_keys_of_fold step4Lower
      step4Lower_inserts hconc_unfold
    have hconc_contains : concDecls.containsKey newDt.name :=
      (hkeys_iff newDt.name).mp hmono_contains
    have hconc_get_ne : concDecls.getByKey newDt.name ≠ none := by
      rw [IndexMap.getByKey_ne_none_iff_containsKey]; exact hconc_contains
    have hconc_get_some : ∃ d, concDecls.getByKey newDt.name = some d := by
      cases hg : concDecls.getByKey newDt.name with
      | none => exact absurd hg hconc_get_ne
      | some d => exact ⟨d, rfl⟩
    have hcn_self_dt : concretizeName newDt.name #[] = newDt.name :=
      concretizeName_empty_args newDt.name
    have hcn_eq2 : concretizeName g_orig args = concretizeName newDt.name #[] := by
      rw [hcn_self_dt, ← hname_eq]
    have hWit_dt : ∃ d, concDecls.getByKey (concretizeName g_orig args) = some d := by
      rw [← hname_eq]; exact hconc_get_some
    obtain ⟨hg_eq, hargs_eq⟩ :=
      hUniqueNames hconc g_orig newDt.name args #[] hcn_eq2 hWit_dt
    have hcn_g : concretizeName g_orig args = g_orig := by
      rw [hargs_eq]; exact concretizeName_empty_args g_orig
    have hdt_name_g : newDt.name = g_orig := by rw [hname_eq]; exact hcn_g
    have hc_nh_mem : c.nameHead ∈ newDt.constructors.map (·.nameHead) :=
      List.mem_map_of_mem hc
    rw [hctors_map, List.mem_map] at hc_nh_mem
    obtain ⟨c_orig, hc_orig_mem, hc_orig_nh⟩ := hc_nh_mem
    have hP := FnMatchP_checkAndSimplify hdecls hts
    have hsrc_dt : decls.getByKey g_orig = some (.dataType dt_orig) :=
      (hP g_orig).2.1 dt_orig hget_orig
    have hsrc_ctor :=
      mkDecls_dt_implies_ctor_keys hdecls g_orig dt_orig hsrc_dt c_orig hc_orig_mem
    rw [hdt_name_g, ← hc_orig_nh] at heq
    rw [heq] at hsrc_ctor
    obtain ⟨f_src, hsrc_f, _⟩ := (hP name).1 tf htyped
    rw [hsrc_f] at hsrc_ctor
    cases hsrc_ctor
  -- Inputs invariant for any newFn at name: NewFnInputsLabelShape +
  -- ConcretizeUniqueNames force the source origin to be tf.
  have hFnInputsAtName : ∀ f' ∈ drained.newFunctions, f'.name = name →
      f'.inputs.map (·.1) = tf.inputs.map (·.1) := by
    intro f' hmem hname_eq
    obtain ⟨g_orig, args, f_orig, hf_name, hget_orig, hin_eq⟩ := hNFI f' hmem
    -- f'.name = concretizeName g_orig args = name = concretizeName name #[].
    have hcn_eq : concretizeName g_orig args = name := by rw [← hf_name]; exact hname_eq
    have hcn_eq2 : concretizeName g_orig args = concretizeName name #[] := by
      rw [hcn_eq]; exact hname_self.symm
    have hWit' : ∃ d, concDecls.getByKey (concretizeName g_orig args) = some d := by
      rw [hcn_eq]; exact hWit
    obtain ⟨hg_eq, _hargs_eq⟩ :=
      hUniqueNames hconc g_orig name args #[] hcn_eq2 hWit'
    -- typedDecls has .function f_orig at g_orig = name; htyped has .function tf at name.
    -- So f_orig = tf.
    rw [hg_eq] at hget_orig
    rw [htyped] at hget_orig
    simp only [Option.some.injEq, Typed.Declaration.function.injEq] at hget_orig
    subst hget_orig
    exact hin_eq
  -- Apply the 3-fold trace.
  rw [PhaseA2.concretizeBuild_eq]
  have h1 := PhaseA2.fromSource_inserts_function_at_key_inputs typedDecls drained.mono htyped htf_params
  have h2 :
      (drained.newDataTypes.foldl (PhaseA2.dtStep drained.mono)
        (typedDecls.pairs.foldl (PhaseA2.srcStep typedDecls drained.mono) default)).getByKey name
      = (typedDecls.pairs.foldl (PhaseA2.srcStep typedDecls drained.mono) default).getByKey name := by
    rw [← Array.foldl_toList]
    apply PhaseA2.dtStep_foldl_no_g_preserves drained.mono drained.newDataTypes.toList _
    · intro dt hdt
      exact hDtNotKey dt (Array.mem_toList_iff.mp hdt)
    · intro dt hdt c hc
      exact hDtCtorNotKey dt (Array.mem_toList_iff.mp hdt) c hc
  -- After dtStep, value at name is unchanged from srcStep output.
  have h3 :
      ∃ md_f, (drained.newDataTypes.foldl (PhaseA2.dtStep drained.mono)
        (typedDecls.pairs.foldl (PhaseA2.srcStep typedDecls drained.mono) default)).getByKey name
        = some (.function md_f) ∧ md_f.inputs.map (·.1) = tf.inputs.map (·.1) := by
    rw [h2]; exact h1
  exact PhaseA2.fnStep_foldl_preserves_function_kind_inputs typedDecls drained.mono
    drained.newFunctions _ hFnInputsAtName h3

/-- Entry-restricted ctor-kind preservation. Mirror of
`concretizeBuild_preserves_function_kind_at_entry_fwd` for `.constructor`
entries. Under `Typed.Decls.ConcretizeUniqueNames` (carried by
`WellFormed.noNameCollisions`), typed `.constructor td_dt td_c` at `name`
with `td_dt.params = []` propagates to `monoDecls` (= `concretizeBuild`
output) carrying `.constructor` at the same key.

Closure path: trace through the three folds of `concretizeBuild`.
* **srcStep-fold** at `(name, .constructor td_dt td_c)` with
  `td_dt.params.isEmpty = true` inserts `.constructor` at `name` (via
  `fromSource_inserts_ctor_at_key`); other source pairs at different keys
  preserve via `srcStep_foldl_no_g_preserves`.
* **dtStep-fold** could overwrite at `name` only if `dt.name = name` for some
  `dt ∈ drained.newDataTypes` (in which case the outer `.dataType` insert
  flips kind); the inner ctor-fold's inserts always produce `.constructor`,
  so kind is preserved unconditionally even when `dt.name.pushNamespace
  c.nameHead = name`. The `dt.name = name` case is ruled out via
  `concretize_drain_preserves_StrongNewNameShape` + `ConcretizeUniqueNames`:
  SNN gives `dt.name = concretizeName g_orig args` for typed `.dataType` at
  `g_orig`; uniqueness forces `g_orig = name`, but typed has
  `.constructor td_dt td_c` at `name` (not `.dataType`), contradiction.
* **fnStep-fold** could overwrite at `name` only if `f.name = name` for some
  `f ∈ drained.newFunctions` (which would flip kind to `.function`). Ruled
  out via SNN + ConcretizeUniqueNames analogously: `f.name = concretizeName
  g_orig args = name = concretizeName name #[]` ⟹ `g_orig = name`, then
  typed has `.function f_orig` at `name` contradicting typed `.constructor`.
-/
theorem concretizeBuild_preserves_ctor_kind_at_entry_fwd
    {t : Source.Toplevel} {decls : Source.Decls}
    {typedDecls : Typed.Decls} {concDecls : Concrete.Decls}
    {drained : DrainState}
    (hdecls : t.mkDecls = .ok decls)
    (hts : t.checkAndSimplify = .ok typedDecls)
    (hdrain : concretizeDrain typedDecls (concretizeDrainFuel typedDecls)
      { pending := concretizeSeed typedDecls, seen := {}, mono := {},
        newFunctions := #[], newDataTypes := #[] } = .ok drained)
    (hconc : typedDecls.concretize = .ok concDecls)
    (hUniqueNames : Typed.Decls.ConcretizeUniqueNames typedDecls)
    {name : Global} {td_dt : DataType} {td_c : Constructor}
    (htyped : typedDecls.getByKey name = some (.constructor td_dt td_c))
    (hdt_params : td_dt.params = []) :
    ∃ md_dt md_c, (concretizeBuild typedDecls drained.mono drained.newFunctions
      drained.newDataTypes).getByKey name = some (.constructor md_dt md_c) := by
  -- StrongNewNameShape preserved through drain.
  have hSNN := concretize_drain_preserves_StrongNewNameShape _ _
    (DrainState.StrongNewNameShape.init typedDecls (concretizeSeed typedDecls)) hdrain
  -- Witness for noNameCollisions: derived FORWARD via insert-only properties of
  -- the three folds + step4Lower keys-iff. srcStep at `(name, .constructor td_dt td_c)`
  -- with `td_dt.params = []` inserts at `name`; dtStep/fnStep folds preserve via
  -- containsKey monotonicity; step4Lower keys-iff lifts to concDecls.
  have hWit : ∃ d, concDecls.getByKey name = some d := by
    have hSrc := PhaseA2.fromSource_inserts_ctor_at_key typedDecls drained.mono
      htyped hdt_params
    obtain ⟨_, _, hSrcGet⟩ := hSrc
    have hSrcContains :
        (typedDecls.pairs.foldl (PhaseA2.srcStep typedDecls drained.mono) default).containsKey
          name :=
      (IndexMap.getByKey_isSome_iff_containsKey _ _).mp (by rw [hSrcGet]; rfl)
    have hDtContains :
        (drained.newDataTypes.foldl (PhaseA2.dtStep drained.mono)
          (typedDecls.pairs.foldl (PhaseA2.srcStep typedDecls drained.mono) default)).containsKey
          name :=
      PhaseA2.dtStep_foldl_preserves_containsKey drained.mono drained.newDataTypes _ hSrcContains
    have hBuildContains : (concretizeBuild typedDecls drained.mono drained.newFunctions
        drained.newDataTypes).containsKey name := by
      rw [PhaseA2.concretizeBuild_eq]
      exact PhaseA2.fnStep_foldl_preserves_containsKey typedDecls drained.mono
        drained.newFunctions _ hDtContains
    have hconc_unfold := hconc
    unfold Typed.Decls.concretize at hconc_unfold
    simp only [bind, Except.bind] at hconc_unfold
    rw [hdrain] at hconc_unfold
    have hkeys_iff := concretize_step_4_keys_of_fold step4Lower
      step4Lower_inserts hconc_unfold
    have hconc_contains : concDecls.containsKey name :=
      (hkeys_iff name).mp hBuildContains
    have hconc_get_ne : concDecls.getByKey name ≠ none := by
      rw [IndexMap.getByKey_ne_none_iff_containsKey]; exact hconc_contains
    cases hg : concDecls.getByKey name with
    | none => exact absurd hg hconc_get_ne
    | some d => exact ⟨d, rfl⟩
  -- name = concretizeName name #[].
  have hname_self : concretizeName name #[] = name := concretizeName_empty_args name
  -- Disjointness for newDataTypes (dt.name ≠ name): SNN + uniqueness.
  have hDtNotKey : ∀ newDt ∈ drained.newDataTypes, newDt.name ≠ name := by
    intro newDt hmem heq
    obtain ⟨g_orig, args, dt_orig, hname_eq, hget_orig, _hargs_sz, _⟩ := hSNN.2 newDt hmem
    -- newDt.name = concretizeName g_orig args = name. So concretizeName g_orig args = name.
    have hcn_eq : concretizeName g_orig args = name := by rw [← hname_eq]; exact heq
    have hcn_eq2 : concretizeName g_orig args = concretizeName name #[] := by
      rw [hcn_eq]; exact hname_self.symm
    have hWit' : ∃ d, concDecls.getByKey (concretizeName g_orig args) = some d := by
      rw [hcn_eq]; exact hWit
    obtain ⟨hg_eq, _⟩ := hUniqueNames hconc g_orig name args #[] hcn_eq2 hWit'
    -- typed has .dataType dt_orig at g_orig = name; but typed has .constructor at name.
    rw [hg_eq] at hget_orig
    rw [htyped] at hget_orig
    cases hget_orig
  -- Disjointness for newFunctions (f.name ≠ name): SNN + uniqueness.
  have hFnNotKey : ∀ newFn ∈ drained.newFunctions, newFn.name ≠ name := by
    intro newFn hmem heq
    obtain ⟨g_orig, args, _f_orig, hf_name, hget_orig, _hargs_sz⟩ := hSNN.1 newFn hmem
    -- newFn.name = concretizeName g_orig args = name.
    have hcn_eq : concretizeName g_orig args = name := by rw [← hf_name]; exact heq
    have hcn_eq2 : concretizeName g_orig args = concretizeName name #[] := by
      rw [hcn_eq]; exact hname_self.symm
    have hWit' : ∃ d, concDecls.getByKey (concretizeName g_orig args) = some d := by
      rw [hcn_eq]; exact hWit
    obtain ⟨hg_eq, _⟩ := hUniqueNames hconc g_orig name args #[] hcn_eq2 hWit'
    -- typed has .function f_orig at g_orig = name; but typed has .constructor at name.
    rw [hg_eq] at hget_orig
    rw [htyped] at hget_orig
    cases hget_orig
  -- Apply existing existential ctor-kind preservation under hDtNotKey + hFnNotKey
  -- (no hCtorNotKey needed: inner ctor-fold's inserts always produce
  -- `.constructor`, so kind is preserved even when dt.name.pushNamespace
  -- c.nameHead = name).
  exact PhaseA2.concretizeBuild_preserves_ctor_kind_fwd typedDecls drained.mono
    drained.newFunctions drained.newDataTypes htyped hdt_params hDtNotKey hFnNotKey

/-! ### PLAN_3B Phase B prerequisites: reverse kind correspondence + ctorIdx +
dtSize agreement. Each is a precisely-named sub-sorry; closed in subsequent
sessions per PLAN_3B.md S5-S7. -/

/-- Helper: `step4Lower` foldlM preserves "no key g" when monoDecls has none at g. -/
theorem step4Lower_fold_preserves_none_at_key
    {monoDecls : Typed.Decls} {concDecls : Concrete.Decls} {g : Global}
    (hmono : monoDecls.getByKey g = none)
    (hfold : monoDecls.foldlM (init := default) step4Lower = .ok concDecls) :
    concDecls.getByKey g = none := by
  rw [IndexMap.indexMap_foldlM_eq_list_foldlM] at hfold
  have hno_g : ∀ p ∈ monoDecls.pairs.toList, (p.1 == g) = false := by
    intro p hp
    rcases hbeq : (p.1 == g) with _ | _
    · rfl
    · exfalso
      have hpkey : p.1 = g := LawfulBEq.eq_of_beq hbeq
      have hpget := IndexMap.getByKey_of_mem_pairs monoDecls p.1 p.2 hp
      rw [hpkey, hmono] at hpget
      cases hpget
  have := step4Lower_foldlM_no_key_preserves _ hno_g _ _ hfold
  rw [this]
  unfold IndexMap.getByKey
  show ((default : Concrete.Decls).indices[g]?).bind _ = none
  have : (default : Concrete.Decls).indices[g]? = none := by
    show ((default : Std.HashMap Global Nat))[g]? = none
    exact Std.HashMap.getElem?_empty
  rw [this]; rfl

/-- `step4Lower` backward direction at the `.dataType` kind. concDecls
.dataType at g → monoDecls .dataType at g. -/
theorem step4Lower_backward_dataType_kind_at_key
    {monoDecls : Typed.Decls} {concDecls : Concrete.Decls}
    {g : Global} {cd_dt : Concrete.DataType}
    (hcd : concDecls.getByKey g = some (.dataType cd_dt))
    (hfold : monoDecls.foldlM (init := default) step4Lower = .ok concDecls) :
    ∃ md_dt, monoDecls.getByKey g = some (.dataType md_dt) := by
  cases hmono : monoDecls.getByKey g with
  | none =>
    exfalso
    have := step4Lower_fold_preserves_none_at_key hmono hfold
    rw [this] at hcd; cases hcd
  | some d_mono =>
    have h := step4Lower_fold_kind_at_key hmono hfold
    cases d_mono with
    | function _ =>
      simp only at h
      obtain ⟨cf, hcf⟩ := h
      rw [hcd] at hcf; cases hcf
    | dataType md_dt => exact ⟨md_dt, rfl⟩
    | constructor _ _ =>
      simp only at h
      obtain ⟨cdt, cc, hcc⟩ := h
      rw [hcd] at hcc; cases hcc

/-- `step4Lower` backward direction at the `.function` kind. concDecls
.function at g → monoDecls .function at g. -/
theorem step4Lower_backward_function_kind_at_key
    {monoDecls : Typed.Decls} {concDecls : Concrete.Decls}
    {g : Global} {cf : Concrete.Function}
    (hcd : concDecls.getByKey g = some (.function cf))
    (hfold : monoDecls.foldlM (init := default) step4Lower = .ok concDecls) :
    ∃ md_f, monoDecls.getByKey g = some (.function md_f) := by
  cases hmono : monoDecls.getByKey g with
  | none =>
    exfalso
    have := step4Lower_fold_preserves_none_at_key hmono hfold
    rw [this] at hcd; cases hcd
  | some d_mono =>
    have h := step4Lower_fold_kind_at_key hmono hfold
    cases d_mono with
    | function md_f => exact ⟨md_f, rfl⟩
    | dataType _ =>
      simp only at h
      obtain ⟨cdt, hcdt⟩ := h
      rw [hcd] at hcdt; cases hcdt
    | constructor _ _ =>
      simp only at h
      obtain ⟨cdt, cc, hcc⟩ := h
      rw [hcd] at hcc; cases hcc

/-- Stage 1 of `_ctor_kind_bwd`: `step4Lower` backward direction at the
`.constructor` kind. concDecls .ctor at g → monoDecls .ctor at g. -/
theorem step4Lower_backward_ctor_kind_at_key
    {monoDecls : Typed.Decls} {concDecls : Concrete.Decls}
    {g : Global} {cd_dt : Concrete.DataType} {cd_c : Concrete.Constructor}
    (hcd : concDecls.getByKey g = some (.constructor cd_dt cd_c))
    (hfold : monoDecls.foldlM (init := default) step4Lower = .ok concDecls) :
    ∃ md_dt md_c, monoDecls.getByKey g = some (.constructor md_dt md_c) := by
  cases hmono : monoDecls.getByKey g with
  | none =>
    exfalso
    have := step4Lower_fold_preserves_none_at_key hmono hfold
    rw [this] at hcd; cases hcd
  | some d_mono =>
    have h := step4Lower_fold_kind_at_key hmono hfold
    cases d_mono with
    | function _ =>
      simp only at h
      obtain ⟨cf, hcf⟩ := h
      rw [hcd] at hcf; cases hcf
    | dataType _ =>
      simp only at h
      obtain ⟨cdt, hcdt⟩ := h
      rw [hcd] at hcdt; cases hcdt
    | constructor md_dt md_c =>
      exact ⟨md_dt, md_c, rfl⟩

-- `concretize_produces_ctorPresent_under_entry` (Wire B) MOVED to SizeBound.lean
-- so it can use `DirectDagBody.concretizeBuild_dataType_origin` (which is in
-- SizeBound and transitively imports Phase4 — moving the consumer downstream
-- breaks the cycle).

/-! ### Tier-A primitive: typed function at concrete-function key forces `params = []`.

Under `WellFormed t`, if both `typedDecls` and `concDecls` carry `.function` at the same
key `g`, then the typed function has empty params. This is the key fact that lets
`concretize_input_pairs_match_wf` (StructCompatible.lean A.4-trade granular sub-bridge)
apply `concretizeBuild_at_typed_function_explicit` (which requires `tf.params = []`).

Closure path:
1. Extract `monoDecls = concretizeBuild typedDecls drained.mono drained.newFunctions
   drained.newDataTypes` from `hconc` so that `monoDecls.foldlM step4Lower = .ok concDecls`.
2. `step4Lower_backward_function_kind_at_key` lifts `concDecls.getByKey g = some (.function _)`
   to `monoDecls.getByKey g = some (.function md_f)`.
3. `concretizeBuild_function_origin` splits into two cases:
   * (A) `typedDecls.getByKey g = some (.function f_src) ∧ f_src.params = []`. Combined
     with `htf` (which says `typedDecls.getByKey g = some (.function tf)`), `f_src = tf`,
     so `tf.params = f_src.params = []`. ✓
   * (B) `∃ f ∈ drained.newFunctions, f.name = g`. Use `StrongNewNameShape.2.1` to extract
     a typed-origin: `g = f.name = concretizeName g_orig args` with
     `typedDecls.getByKey g_orig = some (.function f_orig)` and
     `args.size = f_orig.params.length`. Apply `WellFormed.noNameCollisions` (=
     `ConcretizeUniqueNames`) to the equation `concretizeName g_orig args =
     concretizeName g #[]` (using `concretizeName_empty_args`) with witness from `hcf`
     to get `g_orig = g ∧ args = #[]`. Then `f_orig = tf` (via uniqueness of
     `typedDecls.getByKey g`) and `args.size = 0 = f_orig.params.length` ⇒ `tf.params = []`. ✓

Wired from `concretize_input_pairs_match_wf` and `concretize_extract_concF_flat_size_bridge_wf`
in `Ix/Aiur/Proofs/StructCompatible.lean` (Tier-A.4-trade closure). -/
theorem typed_function_at_concrete_function_key_params_empty
    {t : Source.Toplevel} {decls : Source.Decls}
    {typedDecls : Typed.Decls} {concDecls : Concrete.Decls}
    (hwf : WellFormed t)
    (hdecls : t.mkDecls = .ok decls)
    (hts : t.checkAndSimplify = .ok typedDecls)
    (hconc : typedDecls.concretize = .ok concDecls)
    {g : Global} {tf : Typed.Function} {concF : Concrete.Function}
    (htf : typedDecls.getByKey g = some (.function tf))
    (hcf : concDecls.getByKey g = some (.function concF)) :
    tf.params = [] := by
  -- Step 1: extract monoDecls + drained from hconc.
  have hconc_unfold := hconc
  unfold Typed.Decls.concretize at hconc_unfold
  simp only [bind, Except.bind] at hconc_unfold
  split at hconc_unfold
  · contradiction
  rename_i drained hdrain
  -- Step 2: backward step4Lower lift.
  obtain ⟨md_f, hmono_get⟩ :=
    step4Lower_backward_function_kind_at_key hcf hconc_unfold
  -- Step 3: origin split via concretizeBuild_function_origin.
  rcases DirectDagBody.concretizeBuild_function_origin typedDecls drained.mono
      drained.newFunctions drained.newDataTypes hmono_get with
    ⟨f_src, hsrc_get, hsrc_params⟩ | ⟨f, hf_mem, hf_name⟩
  · -- Case (A): srcStep wrote f_src at g with f_src.params = []. f_src = tf.
    rw [htf] at hsrc_get
    simp only [Option.some.injEq, Typed.Declaration.function.injEq] at hsrc_get
    subst hsrc_get
    exact hsrc_params
  · -- Case (B): some f ∈ newFunctions has f.name = g. Use StrongNewNameShape +
    -- noNameCollisions to identify g with the typed-origin g_orig (and force args = #[]).
    have hSNN := concretize_drain_preserves_StrongNewNameShape _ _
      (DrainState.StrongNewNameShape.init typedDecls (concretizeSeed typedDecls)) hdrain
    obtain ⟨g_orig, args, f_orig, hname_eq, hget_orig, hargs_sz⟩ := hSNN.1 f hf_mem
    -- f.name = g, so g = concretizeName g_orig args.
    have hg_cn : g = concretizeName g_orig args := by rw [← hf_name]; exact hname_eq
    -- g = concretizeName g #[].
    have hcn_self : concretizeName g #[] = g := concretizeName_empty_args g
    -- concretizeName g_orig args = concretizeName g #[].
    have hcn_eq : concretizeName g_orig args = concretizeName g #[] := by
      rw [hcn_self, ← hg_cn]
    -- Witness: concDecls.getByKey (concretizeName g_orig args) = some _.
    have hWit : ∃ d, concDecls.getByKey (concretizeName g_orig args) = some d := by
      rw [← hg_cn]; exact ⟨_, hcf⟩
    -- Apply ConcretizeUniqueNames.
    have hUniqueNames : Typed.Decls.ConcretizeUniqueNames typedDecls :=
      hwf.noNameCollisions typedDecls hts
    obtain ⟨hg_eq, hargs_eq⟩ :=
      hUniqueNames hconc g_orig g args #[] hcn_eq hWit
    -- g_orig = g, so f_orig = tf via uniqueness of typedDecls.getByKey g.
    rw [hg_eq] at hget_orig
    rw [htf] at hget_orig
    simp only [Option.some.injEq, Typed.Declaration.function.injEq] at hget_orig
    -- args = #[] ⟹ args.size = 0 ⟹ tf.params.length = 0 ⟹ tf.params = [].
    have hsz0 : args.size = 0 := by rw [hargs_eq]; rfl
    have hlen0 : tf.params.length = 0 := by
      rw [← hget_orig] at hargs_sz; rw [← hargs_sz]; exact hsz0
    exact List.length_eq_zero_iff.mp hlen0

/-- Helper: under `∃ f ∈ newFunctions, f.name = g`, `fnStep` foldl ends with
`.function` at `g` (every fnStep insert at f.name produces `.function`). -/
theorem fnStep_foldl_with_fname_yields_function
    (typedDecls : Typed.Decls) (mono : MonoMap)
    (newFunctions : Array Typed.Function) (init : Typed.Decls) {g : Global}
    (hex : ∃ f ∈ newFunctions, f.name = g) :
    ∃ newF, (newFunctions.foldl (PhaseA2.fnStep typedDecls mono) init).getByKey g
      = some (.function newF) := by
  rw [← Array.foldl_toList]
  obtain ⟨f, hf_mem, hf_name⟩ := hex
  have hf_mem' : f ∈ newFunctions.toList := Array.mem_toList_iff.mpr hf_mem
  obtain ⟨pre, post, hsplit⟩ := List.append_of_mem hf_mem'
  rw [hsplit]
  rw [List.foldl_append, List.foldl_cons]
  -- mid_acc has .function at g.
  have hmid : ∃ newF, (PhaseA2.fnStep typedDecls mono
      (pre.foldl (PhaseA2.fnStep typedDecls mono) init) f).getByKey g
        = some (.function newF) := by
    unfold PhaseA2.fnStep
    rw [hf_name]
    exact ⟨_, IndexMap.getByKey_insert_self _ _ _⟩
  -- Post fold preserves "some .function at g" since fnStep always inserts .function.
  have hpost : ∀ (xs : List Typed.Function) (acc : Typed.Decls),
      (∃ newF, acc.getByKey g = some (.function newF)) →
      ∃ newF, (xs.foldl (PhaseA2.fnStep typedDecls mono) acc).getByKey g
        = some (.function newF) := by
    intro xs
    induction xs with
    | nil => intro acc h; exact h
    | cons f' rest ih =>
      intro acc h
      simp only [List.foldl_cons]
      apply ih
      by_cases hbeq : (f'.name == g) = true
      · have heq : f'.name = g := LawfulBEq.eq_of_beq hbeq
        unfold PhaseA2.fnStep
        rw [heq]
        exact ⟨_, IndexMap.getByKey_insert_self _ _ _⟩
      · have hne : (f'.name == g) = false := Bool.not_eq_true _ |>.mp hbeq
        obtain ⟨newF, hget⟩ := h
        unfold PhaseA2.fnStep
        exact ⟨newF, by rw [IndexMap.getByKey_insert_of_beq_false _ _ hne]; exact hget⟩
  exact hpost post _ hmid

/-- Reverse Phase A.4: concDecls has `.constructor` at g → source decls has
`.constructor` at g. F=0 closure via `concretizeBuild_ctor_origin` 2-way split:
either source has `.ctor` at `g` directly (FnMatchP backward) or origin 4
holds and `mkDecls_dt_implies_ctor_keys` derives the source ctor key. -/
theorem concretize_under_fullymono_preserves_ctor_kind_bwd
    {t : Source.Toplevel} {decls : Source.Decls}
    {typedDecls : Typed.Decls} {concDecls : Concrete.Decls}
    (hmono : FullyMonomorphic t)
    (hdecls : t.mkDecls = .ok decls)
    (hts : t.checkAndSimplify = .ok typedDecls)
    (hconc : typedDecls.concretize = .ok concDecls)
    {g : Global} {cd_dt : Concrete.DataType} {cd_c : Concrete.Constructor}
    (hcd : concDecls.getByKey g = some (.constructor cd_dt cd_c)) :
    ∃ src_dt src_c, decls.getByKey g = some (.constructor src_dt src_c) := by
  -- Extract drained from hconc.
  unfold Typed.Decls.concretize at hconc
  simp only [bind, Except.bind] at hconc
  split at hconc
  · cases hconc
  rename_i drained hdrain
  -- Stage 1: concrete .ctor at g → mono .ctor at g.
  obtain ⟨md_dt, md_c, hmono_get⟩ := step4Lower_backward_ctor_kind_at_key hcd hconc
  -- Stage 2: classify origin via concretizeBuild_ctor_origin (2-way split).
  rcases PhaseA2.concretizeBuild_ctor_origin typedDecls drained.mono
    drained.newFunctions drained.newDataTypes hmono_get with
    ⟨src_dt_typed, src_c_typed, htd, _hparams⟩ | ⟨dt, hdt_mem, c, hc_mem, hcname⟩
  · -- Origin 1 (.ctor in typed): source has .ctor via FnMatchP backward.
    have hP := FnMatchP_checkAndSimplify hdecls hts
    exact ⟨src_dt_typed, src_c_typed, (hP g).2.2 src_dt_typed src_c_typed htd⟩
  · -- Origin 4: dt.name.pushNamespace c.nameHead = g. Use StrongNewNameShape +
    -- mkDecls_dt_implies_ctor_keys.
    have hSNN := concretize_drain_preserves_StrongNewNameShape _ _
      (DrainState.StrongNewNameShape.init typedDecls (concretizeSeed typedDecls)) hdrain
    obtain ⟨g_orig, args, dt_orig, hname, hget_orig, hargs_sz, hctors⟩ :=
      hSNN.2 dt hdt_mem
    have hdt_params_empty : ∀ k dt', typedDecls.getByKey k = some (.dataType dt') →
      dt'.params = [] := typedDecls_dt_params_empty_of_fullyMonomorphic hmono hdecls hts
    have hdt_orig_params := hdt_params_empty g_orig dt_orig hget_orig
    have hargs_zero : args.size = 0 := by rw [hargs_sz, hdt_orig_params]; rfl
    have hargs_empty : args = #[] := Array.size_eq_zero_iff.mp hargs_zero
    have hname_eq : dt.name = g_orig := by
      rw [hname, hargs_empty]; exact concretizeName_empty_args g_orig
    -- c ∈ dt.constructors → c.nameHead matches some c_orig.nameHead in dt_orig.
    have hmem_map : c.nameHead ∈ dt.constructors.map (·.nameHead) :=
      List.mem_map_of_mem hc_mem
    rw [hctors, List.mem_map] at hmem_map
    obtain ⟨c_orig, hc_orig_mem, hc_orig_nameHead⟩ := hmem_map
    -- Source dt at g_orig (typed dt_orig — by FnMatchP backward).
    have hP := FnMatchP_checkAndSimplify hdecls hts
    have hsrc_dt : decls.getByKey g_orig = some (.dataType dt_orig) :=
      (hP g_orig).2.1 dt_orig hget_orig
    -- mkDecls_dt_implies_ctor_keys: source has .ctor at g_orig.pushNamespace c_orig.nameHead.
    have hsrc_ctor :=
      mkDecls_dt_implies_ctor_keys hdecls g_orig dt_orig hsrc_dt c_orig hc_orig_mem
    -- Show g_orig.pushNamespace c_orig.nameHead = g.
    have hkey_eq : g_orig.pushNamespace c_orig.nameHead = g := by
      rw [hc_orig_nameHead, ← hname_eq]
      exact hcname
    rw [hkey_eq] at hsrc_ctor
    exact ⟨dt_orig, c_orig, hsrc_ctor⟩

/-- Phase B main: ctor-index agreement under FullyMono. -/
theorem concretize_under_fullymono_ctor_idx_agree
    {t : Source.Toplevel} {decls : Source.Decls}
    {typedDecls : Typed.Decls} {concDecls : Concrete.Decls}
    (hmono : FullyMonomorphic t)
    (hdecls : t.mkDecls = .ok decls)
    (hts : t.checkAndSimplify = .ok typedDecls)
    (hconc : typedDecls.concretize = .ok concDecls)
    {g : Global}
    {src_dt : DataType} {src_c : Constructor}
    {cd_dt : Concrete.DataType} {cd_c : Concrete.Constructor}
    (hsrc : decls.getByKey g = some (.constructor src_dt src_c))
    (hcd : concDecls.getByKey g = some (.constructor cd_dt cd_c)) :
    src_dt.constructors.findIdx? (· == src_c) =
      cd_dt.constructors.findIdx? (· == cd_c) := by
  -- A.1 forward: source has ctor at g → typed has ctor at g (with same dt+c
  -- after canceling via FnMatchP backward).
  obtain ⟨td_dt, td_c, htd⟩ := checkAndSimplify_preserves_ctor_kind_fwd hdecls hts hsrc
  have hP := FnMatchP_checkAndSimplify hdecls hts
  have hsrc_again : decls.getByKey g = some (.constructor td_dt td_c) :=
    (hP g).2.2 td_dt td_c htd
  rw [hsrc] at hsrc_again
  have ⟨htd_dt_eq, htd_c_eq⟩ : src_dt = td_dt ∧ src_c = td_c := by
    simp only [Option.some.injEq, Source.Declaration.constructor.injEq] at hsrc_again
    exact hsrc_again
  -- Rewrite htd to use src_dt/src_c (substitute td_dt → src_dt, td_c → src_c).
  rw [← htd_dt_eq, ← htd_c_eq] at htd
  clear htd_dt_eq htd_c_eq
  -- Now `htd : typedDecls.getByKey g = some (.constructor src_dt src_c)`.
  -- Source dt at src_dt.name (via mkDecls_ctor_companion).
  obtain ⟨hsrc_dt, hcmem⟩ := mkDecls_ctor_companion hdecls g src_dt src_c hsrc
  -- Typed dt at src_dt.name.
  obtain ⟨td_dt', htd_dt'⟩ := checkAndSimplify_src_dt_to_td hdecls hts hsrc_dt
  have htd_dt_eq : td_dt' = src_dt := by
    have := (hP src_dt.name).2.1 td_dt' htd_dt'
    rw [hsrc_dt] at this; cases this; rfl
  rw [htd_dt_eq] at htd_dt'
  -- Distinctness on src_dt.constructors nameHeads.
  have hdistinct := mkDecls_dt_ctor_nameheads_distinct hdecls src_dt.name src_dt hsrc_dt
  -- Position of src_c in src_dt.constructors (full structural).
  obtain ⟨i, hi_lt, hi_eq⟩ := List.getElem_of_mem hcmem
  -- Uniqueness via distinctness on nameHeads.
  have hi_unique : ∀ j (hj : j < src_dt.constructors.length),
      (src_dt.constructors[j]'hj) = src_c → j = i := by
    intro j hj heq
    apply hdistinct j i hj hi_lt
    rw [heq, ← hi_eq]
  -- src side findIdx? = some i.
  have hsrc_findIdx :
      src_dt.constructors.findIdx? (· == src_c) = some i := by
    rw [List.findIdx?_eq_some_iff_getElem]
    refine ⟨hi_lt, ?_, ?_⟩
    · show (src_dt.constructors[i]'hi_lt == src_c) = true
      rw [hi_eq]; exact BEq.rfl
    · intro j hji
      show ¬((src_dt.constructors[j]'(Nat.lt_trans hji hi_lt)) == src_c) = true
      intro hbeq
      have hj_eq : (src_dt.constructors[j]'(Nat.lt_trans hji hi_lt)) = src_c :=
        LawfulBEq.eq_of_beq hbeq
      have := hi_unique j (Nat.lt_trans hji hi_lt) hj_eq
      omega
  -- Phase A.2 + A.3: derive cd_dt structure with positional info.
  -- Unfold concretize to get drained.
  unfold Typed.Decls.concretize at hconc
  simp only [bind, Except.bind] at hconc
  split at hconc
  · cases hconc
  rename_i drained hdrain
  -- FullyMono → params empty for fns and dts.
  have hfn_params_empty : ∀ k f, typedDecls.getByKey k = some (.function f) → f.params = [] :=
    typedDecls_params_empty_of_fullyMonomorphic hmono hdecls hts
  have hdt_params_empty : ∀ k dt', typedDecls.getByKey k = some (.dataType dt') → dt'.params = [] :=
    typedDecls_dt_params_empty_of_fullyMonomorphic hmono hdecls hts
  -- StrongNewNameShape preserved through drain.
  have hSNN := concretize_drain_preserves_StrongNewNameShape _ _
    (DrainState.StrongNewNameShape.init typedDecls (concretizeSeed typedDecls)) hdrain
  -- Bridge fact `g = src_dt.name.pushNamespace src_c.nameHead`:
  -- source has `.ctor src_dt src_c` at the pushed key (via
  -- `mkDecls_dt_implies_ctor_keys`) and at `g` (via `hsrc`). For mkDecls'
  -- output, ctor entries are inserted ONLY at pushed keys, so g IS the pushed
  -- key. We derive this via re-applying mkDecls_ctor_companion at the pushed
  -- key + using IndexMap.pairs_toList_keys_unique on the SAME pair.
  have hsrc_pushed := mkDecls_dt_implies_ctor_keys hdecls src_dt.name src_dt hsrc_dt src_c hcmem
  have hg_pushed : g = src_dt.name.pushNamespace src_c.nameHead :=
    mkDecls_source_ctor_is_key hdecls g src_dt src_c hsrc
  -- Apply concretizeBuild_at_typed_ctor_explicit_general (with hg_pushed).
  obtain ⟨md_dt, md_c, hmono_get, hLen_md, hNH_md, hPos_md, hStruct_md⟩ :=
    PhaseA2.concretizeBuild_at_typed_ctor_explicit_general typedDecls drained
      hSNN hfn_params_empty hdt_params_empty hg_pushed htd htd_dt' hcmem hdistinct
  -- Apply step4Lower_constructor_explicit to bridge mono → cd.
  obtain ⟨cd_dt', cd_c', hcd', _hName_cd, hLen_cd, hNH_cd, hPos_cd, hStruct_cd, _hCtors_cd⟩ :=
    step4Lower_constructor_explicit hmono_get hconc
  -- cd_dt' = cd_dt and cd_c' = cd_c (via uniqueness at g).
  rw [hcd] at hcd'
  obtain ⟨hcd_dt_eq, hcd_c_eq⟩ : cd_dt' = cd_dt ∧ cd_c' = cd_c := by
    simp only [Option.some.injEq, Concrete.Declaration.constructor.injEq] at hcd'
    exact ⟨hcd'.1.symm, hcd'.2.symm⟩
  rw [hcd_dt_eq] at hLen_cd hPos_cd hStruct_cd
  rw [hcd_c_eq] at hStruct_cd
  -- Get md_dt[i] = md_c via hStruct_md (positional structural equality).
  obtain ⟨hi_lt_md, hi_md_eq⟩ := hStruct_md i hi_lt hi_eq
  -- Get cd_dt[i] = cd_c via hStruct_cd.
  have hi_lt_cd : i < cd_dt.constructors.length := by
    rw [hLen_cd]; exact hi_lt_md
  have hi_cd_eq : (cd_dt.constructors[i]'hi_lt_cd) = cd_c :=
    hStruct_cd i hi_lt_md hi_lt_cd hi_md_eq
  -- Length agreement: cd_dt.length = src_dt.length.
  have hLen_cs : cd_dt.constructors.length = src_dt.constructors.length := by
    rw [hLen_cd, hLen_md]
  -- Distinctness on cd_dt.constructors nameHeads, transferred via positional
  -- nameHead correspondence cd → md → src.
  have hcd_distinct : ∀ a b (ha : a < cd_dt.constructors.length)
      (hb : b < cd_dt.constructors.length),
      (cd_dt.constructors[a]'ha).nameHead = (cd_dt.constructors[b]'hb).nameHead → a = b := by
    intro a b ha hb hab_nh
    have ha_md : a < md_dt.constructors.length := by rw [← hLen_cd]; exact ha
    have hb_md : b < md_dt.constructors.length := by rw [← hLen_cd]; exact hb
    have ha_src : a < src_dt.constructors.length := by rw [← hLen_md]; exact ha_md
    have hb_src : b < src_dt.constructors.length := by rw [← hLen_md]; exact hb_md
    -- Chain nameHeads: cd[a].nh = md[a].nh = src[a].nh.
    have hPos_md_a := (hPos_md a ha_src).2
    have hPos_md_b := (hPos_md b hb_src).2
    have hPos_cd_a := hPos_cd a ha_md ha
    have hPos_cd_b := hPos_cd b hb_md hb
    -- cd[a].nh = md[a].nh = src[a].nh.
    have ha_total : (cd_dt.constructors[a]'ha).nameHead =
        (src_dt.constructors[a]'ha_src).nameHead := by
      rw [hPos_cd_a, hPos_md_a]
    have hb_total : (cd_dt.constructors[b]'hb).nameHead =
        (src_dt.constructors[b]'hb_src).nameHead := by
      rw [hPos_cd_b, hPos_md_b]
    have hsrc_nh : (src_dt.constructors[a]'ha_src).nameHead =
        (src_dt.constructors[b]'hb_src).nameHead := by
      rw [← ha_total, ← hb_total]; exact hab_nh
    exact hdistinct a b ha_src hb_src hsrc_nh
  -- cd side findIdx? = some i.
  have hcd_findIdx :
      cd_dt.constructors.findIdx? (· == cd_c) = some i := by
    rw [List.findIdx?_eq_some_iff_getElem]
    refine ⟨hi_lt_cd, ?_, ?_⟩
    · show (cd_dt.constructors[i]'hi_lt_cd == cd_c) = true
      rw [hi_cd_eq]; exact BEq.rfl
    · intro j hji
      show ¬((cd_dt.constructors[j]'(Nat.lt_trans hji hi_lt_cd)) == cd_c) = true
      intro hbeq
      have hj_eq : (cd_dt.constructors[j]'(Nat.lt_trans hji hi_lt_cd)) = cd_c :=
        LawfulBEq.eq_of_beq hbeq
      -- nameHeads agree → j = i via cd_distinct.
      have hj_nh : (cd_dt.constructors[j]'(Nat.lt_trans hji hi_lt_cd)).nameHead =
          (cd_dt.constructors[i]'hi_lt_cd).nameHead := by
        rw [hj_eq, hi_cd_eq]
      have := hcd_distinct j i (Nat.lt_trans hji hi_lt_cd) hi_lt_cd hj_nh
      omega
  -- Combine.
  rw [hsrc_findIdx, hcd_findIdx]

-- RefClosed decomposition + entry bridge moved to
-- `ConcretizeSound/RefClosed.lean` 2026-04-29.


end Aiur

end -- public section
