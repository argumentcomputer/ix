module
public import Ix.Aiur.Proofs.ConcretizeSound
public import Ix.Aiur.Proofs.ConcretizeSound.Phase4

/-!
`Concrete.Decls.RefClosed` decomposition: Phase C flat-size scaffolding
+ L1/L2/L3 + `NewDeclTypesRefsOk` drain invariant + composition + entry
bridge. Extracted from `ConcretizeSound.lean` 2026-04-29.
-/

public section

namespace Aiur

open Source

/-! #### Phase C scaffolding (F=0): per-`Typ` flat-size correspondence.

The dataType-level theorem `concretize_under_fullymono_dt_flat_size_agree`
factors through a per-`Typ` correspondence: for any source `Typ` and the
`Concrete.Typ` it concretizes to (via `typToConcrete ∘ rewriteTyp emptySubst
drained.mono`, which under `FullyMonomorphic` collapses since args = #[]),
`typFlatSize decls {} ty = Concrete.typFlatSize concDecls {} cty`.

The scaffolding here defines:
1. Fuel-zero base lemma — proven (both sides return 0 at fuel 0 for non-dt
   typs; dt-side returns 1 at fuel 0).
2. Leaf-arm lemma — non-recursive arms (unit/field/pointer/function/mvar)
   evaluate to closed-form constants matching their concrete counterparts.

The full mutual-induction theorem (induction on fuel + structural Typ + dt)
remains future work; its statement is captured in the `TypFlatSizeAgreeFM`
predicate below for downstream consumers to cite.

`Source.Typ.MatchesConcreteFM` and `Source.Decls.DeclsAgreeOnDtFM` are
defined upstream in `ConcretizeSound/MatchesConcrete.lean` (hoisted
2026-05-04) so they are accessible from `Layout.lean` for the per-`Typ`-pair
sibling lemma feeding the `dataTypeFlatSize`-vs-`typLevel` Layout-chain
induction core. -/

-- `Typed.Typ.AppRefToDt` moved upstream to `Ix/Aiur/Semantics/WellFormed.lean`
-- (2026-05-04) so `WellFormed` can host a parallel body-position field.

/-- Fuel-zero base case: both `typFlatSizeBound` and `Concrete.typFlatSizeBound`
return `0` at fuel `0`. F=0 leaf. -/
theorem typFlatSizeBound_zero_eq
    (decls : Source.Decls) (cd : Concrete.Decls)
    (visited : Std.HashSet Global) (visited' : Std.HashSet Global)
    (ty : Typ) (cty : Concrete.Typ) :
    typFlatSizeBound decls 0 visited ty =
      Concrete.typFlatSizeBound cd 0 visited' cty := by
  unfold typFlatSizeBound Concrete.typFlatSizeBound
  rfl

/-- Fuel-zero base case for `dataTypeFlatSizeBound`: both sides return `1`. -/
theorem dataTypeFlatSizeBound_zero_eq
    (decls : Source.Decls) (cd : Concrete.Decls)
    (visited : Std.HashSet Global) (visited' : Std.HashSet Global)
    (dt : DataType) (cd_dt : Concrete.DataType) :
    dataTypeFlatSizeBound decls 0 visited dt =
      Concrete.dataTypeFlatSizeBound cd 0 visited' cd_dt := by
  unfold dataTypeFlatSizeBound Concrete.dataTypeFlatSizeBound
  rfl

/-- Leaf arms of `typFlatSizeBound` that evaluate to closed-form constants
under any positive fuel. F=0; documents the expected sizes for the
non-recursive arms. -/
theorem typFlatSizeBound_leaf_unit
    (decls : Source.Decls) (cd : Concrete.Decls) (n : Nat)
    (V : Std.HashSet Global) (V' : Std.HashSet Global) :
    typFlatSizeBound decls (n+1) V .unit =
      Concrete.typFlatSizeBound cd (n+1) V' .unit := by
  unfold typFlatSizeBound Concrete.typFlatSizeBound
  rfl

theorem typFlatSizeBound_leaf_field
    (decls : Source.Decls) (cd : Concrete.Decls) (n : Nat)
    (V : Std.HashSet Global) (V' : Std.HashSet Global) :
    typFlatSizeBound decls (n+1) V .field =
      Concrete.typFlatSizeBound cd (n+1) V' .field := by
  unfold typFlatSizeBound Concrete.typFlatSizeBound
  rfl

theorem typFlatSizeBound_leaf_pointer
    (decls : Source.Decls) (cd : Concrete.Decls) (n : Nat)
    (V : Std.HashSet Global) (V' : Std.HashSet Global)
    (t : Typ) (ct : Concrete.Typ) :
    typFlatSizeBound decls (n+1) V (.pointer t) =
      Concrete.typFlatSizeBound cd (n+1) V' (.pointer ct) := by
  unfold typFlatSizeBound Concrete.typFlatSizeBound
  rfl

theorem typFlatSizeBound_leaf_function
    (decls : Source.Decls) (cd : Concrete.Decls) (n : Nat)
    (V : Std.HashSet Global) (V' : Std.HashSet Global)
    (ins : List Typ) (out : Typ)
    (cins : List Concrete.Typ) (cout : Concrete.Typ) :
    typFlatSizeBound decls (n+1) V (.function ins out) =
      Concrete.typFlatSizeBound cd (n+1) V' (.function cins cout) := by
  unfold typFlatSizeBound Concrete.typFlatSizeBound
  rfl

-- MOVED to Scratch.lean 2026-04-30 (orphan, FullyMono-dependent):
-- `concretize_under_fullymono_dt_flat_size_agree`,
-- `flatten_agree_under_fullymono`.

/-! ### Decomposition of `concretize_produces_refClosed`. -/

/-! Ported from `Ix/Aiur/Proofs/RefClosedBodyScratch.lean` on 2026-04-24. The
scratch file imported `CheckSound` and `CompilerProgress` (downstream of this
file), so the 3 auxiliary lemmas are kept as local `sorry`s here rather than
re-imported. Their discharge paths are documented inline — each cites
well-formedness / concretize bridge infrastructure that lives downstream. -/
namespace RefClosedBody

/-! #### L1: every typed `.ref g'` points at a typed dt-key. -/

/-- `TypRefsAreDtKeys tds t` — every `.ref g'` in `t` (at checker-visible
positions) has `tds.getByKey g' = some (.dataType _)`. Parallels
`Concrete.Typ.RefClosed`.

`.function` and `.mvar` are treated as opaque leaves because
`wellFormedDecls.wellFormedType` (the source-side checker) does not recurse
into them. Downstream consumers (L3 / `RefTargetsInTds`) also treat
function types opaquely, so no propagation is needed. -/
inductive TypRefsAreDtKeys (tds : Typed.Decls) : Typ → Prop
  | unit    : TypRefsAreDtKeys tds .unit
  | field   : TypRefsAreDtKeys tds .field
  | mvar n  : TypRefsAreDtKeys tds (.mvar n)
  | pointer {inner} (h : TypRefsAreDtKeys tds inner) : TypRefsAreDtKeys tds (.pointer inner)
  | function {ins out}
      (hi : ∀ t ∈ ins, TypRefsAreDtKeys tds t)
      (ho : TypRefsAreDtKeys tds out) :
      TypRefsAreDtKeys tds (.function ins out)
  | tuple {ts} (h : ∀ t ∈ ts.toList, TypRefsAreDtKeys tds t) :
      TypRefsAreDtKeys tds (.tuple ts)
  | array {t n} (h : TypRefsAreDtKeys tds t) : TypRefsAreDtKeys tds (.array t n)
  | ref {g} (hdt : ∃ dt, tds.getByKey g = some (.dataType dt)) :
      TypRefsAreDtKeys tds (.ref g)
  | app {g args}
      (hdt : ∃ dt, tds.getByKey g = some (.dataType dt) ∧
                   args.size = dt.params.length)
      (h : ∀ t ∈ args.toList, TypRefsAreDtKeys tds t) :
      TypRefsAreDtKeys tds (.app g args)

/-- Every typed declaration's types have `.ref` targets that are dt-keys of
`tds`. -/
def AllRefsAreDtKeys (tds : Typed.Decls) : Prop :=
  ∀ name d, tds.getByKey name = some d →
    match d with
    | .function f =>
        (∀ lt ∈ f.inputs, TypRefsAreDtKeys tds lt.snd) ∧
        TypRefsAreDtKeys tds f.output
    | .dataType dt =>
        ∀ c ∈ dt.constructors, ∀ t ∈ c.argTypes, TypRefsAreDtKeys tds t
    | .constructor _ c =>
        ∀ t ∈ c.argTypes, TypRefsAreDtKeys tds t

/-- **L1**: under `FullyMono + checkAndSimplify`, every `.ref g'` in a `tds`
type points to a tds dt-key.

**Discharge path** (~300-400 LoC new infra):

Pipeline: `checkAndSimplify = mkDecls >>= wellFormedDecls >>= typecheckFold >>= simplifyDecls`.

Phase 1 — source-side reflection (CheckSound):
1. Unfold `hts` to extract `hdecls : t.mkDecls = .ok decls`, `hwf :
   wellFormedDecls decls = .ok ()`, `hfold : decls.foldlM (init := default)
   (typecheck step) = .ok midTyped`, `hsimp : simplifyDecls decls midTyped =
   .ok tds`.
2. Reflect `hwf` per-decl via `List.foldlM_except_witnesses` (Lib.lean):
   for every `(name, decl) ∈ decls.pairs.toList`, there exists some visited
   state under which `EStateM.run (wellFormedDecl decl) visited = .ok (...)`.
3. Induct on `wellFormedType [] τ` (structural): `.ref g` arm requires
   `decls.getByKey g = some (.dataType dt)` (since `params = []` under
   `FullyMono` rules out the param-match branch). Conclude a source-side
   `SrcTypRefsAreDtKeys decls t` predicate.

Phase 2 — bridge source → typed:
1. `typecheckFold` preserves types structurally: `.dataType d → .dataType d`
   and `.constructor d c → .constructor d c` (identity inserts); `.function
   f → .function ({f with body := body'})` (only body changes via
   `checkFunction` + zonk).
2. Therefore source `.ref g` targets in types survive to typed types (via a
   `Td*P`-style preservation predicate parallel to `TdDtParamsMatchP`).
3. `simplifyDecls` only rewrites function bodies, not types (Check.lean:125-
   130: datatypes/constructors pass through unchanged; functions only body').
4. Conclude `AllRefsAreDtKeys tds`.

Phase 3 — tie the knot:
1. Source dt-key `decls.getByKey g = some (.dataType dt)` with `dt.params =
   []` via `SrcDtParamsMonoP_mkDecls` (already proved).
2. Typed dt-key `tds.getByKey g = some (.dataType dt')` via
   `TdDtParamsMatchP` or similar; if needed, strengthen to `dt.constructors
   = dt'.constructors` (datatypes pass through unchanged).

BLOCKED ON: see sub-sorries inside `L1_typed_ref_target_is_tds_dtkey`'s
`.dataType` and `.constructor` arms — specifically the
"freshness of visited hashset" lemma and the "constructor companions exist
in mkDecls output" lemma. Infrastructure for the `.function` arm is
complete (closes F=0 there). -/
def _l1_docstub : Unit := ()

/-- Transport a source-side `SrcTypRefsAreDtKeys` witness to a typed-side
`TypRefsAreDtKeys` witness, given that every `.dataType`-at-key in source
decls survives to a `.dataType`-at-key in typed decls (via
`checkAndSimplify_src_dt_to_td`). Specialised to the `params = []` source
context (existing call sites only ever supply this). -/
theorem TypRefsAreDtKeys_of_SrcTypRefsAreDtKeys
    {t : Source.Toplevel} {decls : Source.Decls} {tds : Typed.Decls}
    (hdecls : t.mkDecls = .ok decls)
    (hts : t.checkAndSimplify = .ok tds) :
    ∀ (τ : Typ), SrcTypRefsAreDtKeys decls [] τ → TypRefsAreDtKeys tds τ
  | .unit, _ => .unit
  | .field, _ => .field
  | .mvar n, _ => .mvar n
  | .function ins out, h => by
    cases h with
    | func hi ho =>
      refine .function ?_ ?_
      · intro t htmem
        exact TypRefsAreDtKeys_of_SrcTypRefsAreDtKeys hdecls hts t (hi t htmem)
      · exact TypRefsAreDtKeys_of_SrcTypRefsAreDtKeys hdecls hts out ho
  | .pointer inner, h => by
    cases h with
    | pointer hinner =>
      exact .pointer (TypRefsAreDtKeys_of_SrcTypRefsAreDtKeys hdecls hts inner hinner)
  | .array t n, h => by
    cases h with
    | array ht =>
      exact .array (TypRefsAreDtKeys_of_SrcTypRefsAreDtKeys hdecls hts t ht)
  | .ref g, h => by
    cases h with
    | ref hdt =>
      obtain ⟨dt, hget, _⟩ := hdt
      obtain ⟨dt', hget'⟩ := checkAndSimplify_src_dt_to_td hdecls hts hget
      exact .ref ⟨dt', hget'⟩
    | refTypeParam hin =>
      -- params = [] ⇒ List.any [] is false; contradiction.
      exact absurd hin (by simp)
  | .tuple ts, h => by
    cases h with
    | tuple htsubs =>
      refine .tuple ?_
      intro t htmem
      have hmem_arr : t ∈ ts := Array.mem_toList_iff.mp htmem
      exact TypRefsAreDtKeys_of_SrcTypRefsAreDtKeys hdecls hts t (htsubs t htmem)
  | .app g args, h => by
    cases h with
    | app hdt_src hargs =>
      obtain ⟨dt, hget, hsize_eq⟩ := hdt_src
      obtain ⟨dt', hget'⟩ := checkAndSimplify_src_dt_to_td hdecls hts hget
      -- TdDtParamsMatchP: typed dt' at g maps back to source dt' at g (same dt').
      have hP := TdDtParamsMatchP_checkAndSimplify hdecls hts
      have hsrc_again : decls.getByKey g = some (.dataType dt') := hP g dt' hget'
      have hdt_eq : dt = dt' := by
        rw [hget] at hsrc_again
        cases hsrc_again; rfl
      refine .app ⟨dt', hget', ?_⟩ ?_
      · rw [← hdt_eq]; exact hsize_eq
      · intro t htmem
        have hmem_arr : t ∈ args := Array.mem_toList_iff.mp htmem
        exact TypRefsAreDtKeys_of_SrcTypRefsAreDtKeys hdecls hts t (hargs t htmem)
  termination_by τ => sizeOf τ
  decreasing_by
    all_goals first
      | decreasing_tactic
      | (have := Array.sizeOf_lt_of_mem ‹hmem_arr›; grind)

/-- L1 arms for `.dataType` and `.constructor` source entries: for every
typed `.dataType dt` (or `.constructor dt c`) entry, every ctor argtype
satisfies `TypRefsAreDtKeys tds`. Proved via source-side reflection:
`wellFormedDecls_reflect_dataType_fresh` gives a fresh-visited witness at
the unique source pair (keyed by `dt.name`), which exposes ctor-argtype
well-formedness; then `TypRefsAreDtKeys_of_SrcTypRefsAreDtKeys` transports
to the typed side. The `.constructor` arm reduces to `.dataType` via
`mkDecls_ctor_companion`. -/
theorem L1_dt_and_ctor_arms
    {t : Source.Toplevel} {decls : Source.Decls} {tds : Typed.Decls}
    (hmono : FullyMonomorphic t)
    (hdecls : t.mkDecls = .ok decls)
    (hts : t.checkAndSimplify = .ok tds) :
    (∀ name dt, tds.getByKey name = some (.dataType dt) →
      ∀ c ∈ dt.constructors, ∀ ty ∈ c.argTypes, TypRefsAreDtKeys tds ty) ∧
    (∀ name dt c, tds.getByKey name = some (.constructor dt c) →
      ∀ ty ∈ c.argTypes, TypRefsAreDtKeys tds ty) := by
  have hwfUnit : wellFormedDecls decls = .ok () :=
    checkAndSimplify_implies_wellFormedDecls hdecls hts
  have hdtKey := mkDecls_dt_key_is_name hdecls
  have hCtorCompanion := mkDecls_ctor_companion hdecls
  -- Helper: given a source `.dataType dt_src` entry at `name`, produce the
  -- ctor-argtype well-formedness (source-side) using the fresh-visited lemma.
  have hdtArgs_src : ∀ g dt_src,
      decls.getByKey g = some (.dataType dt_src) →
      ∀ c ∈ dt_src.constructors, ∀ ty ∈ c.argTypes,
        wellFormedDecls.wellFormedType decls dt_src.params ty = .ok () := by
    intro g dt_src hget_src c hcmem ty htmem
    have hmem_src : (g, Source.Declaration.dataType dt_src) ∈ decls.pairs.toList :=
      IndexMap.mem_pairs_of_getByKey _ _ _ hget_src
    obtain ⟨vis, vis', hvis_fresh, hstep⟩ :=
      wellFormedDecls_reflect_dataType_fresh hdtKey hwfUnit hmem_src
    exact wellFormedDecls_reflect_dataType hvis_fresh hstep c hcmem ty htmem
  refine ⟨?_, ?_⟩
  · -- `.dataType` arm.
    intro name dt_td hget_td c hcmem ty htmem
    -- Get source dt entry (same dt by TdDtParamsMatchP).
    have hget_src : decls.getByKey name = some (.dataType dt_td) :=
      checkAndSimplify_dt_in_source hdecls hts hget_td
    have hdtp : dt_td.params = [] :=
      mkDecls_dt_params_empty_of_fullyMonomorphic hmono hdecls name dt_td hget_src
    have hty_wf := hdtArgs_src name dt_td hget_src c hcmem ty htmem
    rw [hdtp] at hty_wf
    have hSrc := SrcTypRefsAreDtKeys_of_wellFormedType decls [] ty hty_wf
    exact TypRefsAreDtKeys_of_SrcTypRefsAreDtKeys hdecls hts ty hSrc
  · -- `.constructor` arm.
    intro name dt_td c_td hget_td ty htmem
    -- Reduce to the dt arm via ctor-companion.
    have hget_src : decls.getByKey name = some (.constructor dt_td c_td) :=
      checkAndSimplify_ctor_in_source hdecls hts hget_td
    obtain ⟨hdt_src, hc_in_dt⟩ := hCtorCompanion name dt_td c_td hget_src
    have hdtp : dt_td.params = [] :=
      mkDecls_dt_params_empty_of_fullyMonomorphic hmono hdecls dt_td.name dt_td hdt_src
    have hty_wf := hdtArgs_src dt_td.name dt_td hdt_src c_td hc_in_dt ty htmem
    rw [hdtp] at hty_wf
    have hSrc := SrcTypRefsAreDtKeys_of_wellFormedType decls [] ty hty_wf
    exact TypRefsAreDtKeys_of_SrcTypRefsAreDtKeys hdecls hts ty hSrc

theorem L1_typed_ref_target_is_tds_dtkey
    {t : Source.Toplevel} {tds : Typed.Decls}
    (hmono : FullyMonomorphic t)
    (hts : t.checkAndSimplify = .ok tds) :
    AllRefsAreDtKeys tds := by
  -- Unfold hts via mkDecls success witness.
  have hts_raw := hts
  unfold Source.Toplevel.checkAndSimplify at hts_raw
  simp only [bind, Except.bind] at hts_raw
  split at hts_raw
  · exact absurd hts_raw (by intro h'; cases h')
  rename_i decls hdecls
  have hwfUnit : wellFormedDecls decls = .ok () :=
    checkAndSimplify_implies_wellFormedDecls hdecls hts
  -- Retrieve the dt- and ctor-arm witnesses via the L1-residual lemma.
  obtain ⟨hDtArm, hCtorArm⟩ := L1_dt_and_ctor_arms hmono hdecls hts
  -- Now establish AllRefsAreDtKeys.
  intro name d hget_td
  cases hd : d with
  | function tf =>
    subst hd
    -- `.function` arm — F=0, closed via source well-formedness reflection.
    obtain ⟨fsrc, hfsrc, hinputs⟩ := checkAndSimplify_fn_in_source hdecls hts hget_td
    have houtput := checkAndSimplify_preserves_output hdecls hts hfsrc hget_td
    have hmem_src : (name, Source.Declaration.function fsrc) ∈ decls.pairs.toList :=
      IndexMap.mem_pairs_of_getByKey _ _ _ hfsrc
    obtain ⟨vis, vis', hstep⟩ := wellFormedDecls_reflect_pair hwfUnit name _ hmem_src
    have ⟨houtput_ok, hinputs_ok⟩ := wellFormedDecls_reflect_function hstep
    have hfparams : fsrc.params = [] :=
      mkDecls_fn_params_empty_of_fullyMonomorphic hmono hdecls name fsrc hfsrc
    rw [hfparams] at houtput_ok hinputs_ok
    refine ⟨?_, ?_⟩
    · intro lt hltmem
      have hlt_src : lt ∈ fsrc.inputs := by rw [← hinputs]; exact hltmem
      have hlt_wf := hinputs_ok lt hlt_src
      have hSrc := SrcTypRefsAreDtKeys_of_wellFormedType decls [] lt.2 hlt_wf
      exact TypRefsAreDtKeys_of_SrcTypRefsAreDtKeys hdecls hts lt.2 hSrc
    · rw [houtput]
      have hSrc := SrcTypRefsAreDtKeys_of_wellFormedType decls [] fsrc.output houtput_ok
      exact TypRefsAreDtKeys_of_SrcTypRefsAreDtKeys hdecls hts fsrc.output hSrc
  | dataType dt =>
    subst hd
    exact hDtArm name dt hget_td
  | constructor dt c =>
    subst hd
    exact hCtorArm name dt c hget_td

/-! #### L2: every tds dt-key survives to cd. -/

/-- Default `Typed.Decls` returns `none` on any `getByKey`. -/
theorem default_typedDecls_getByKey_none (g : Global) :
    (default : Typed.Decls).getByKey g = none := by
  unfold IndexMap.getByKey
  show ((default : Typed.Decls).indices[g]?).bind _ = none
  have : (default : Typed.Decls).indices[g]? = none := by
    show ((default : Std.HashMap Global Nat))[g]? = none
    exact Std.HashMap.getElem?_empty
  rw [this]; rfl

/-- **L2 Phase 1** (`fromSource` fold): if `tds.getByKey g = some (.dataType dt_tds)`
with `dt_tds.params = []`, then after the source-reducing fold,
`getByKey g` still yields a `.dataType _`. -/
theorem L2_phase1_fromSource
    (tds : Typed.Decls) (mono : MonoMap)
    {g : Global} {dt_tds : DataType}
    (hget_g : tds.getByKey g = some (.dataType dt_tds))
    (hparams : dt_tds.params = []) :
    let emptySubst : Global → Option Typ := fun _ => none
    let fromSource : Typed.Decls := tds.pairs.foldl
      (fun acc p =>
        let (key, d) := p
        match d with
        | .function f =>
          if f.params.isEmpty then
            let newInputs := f.inputs.map fun (l, t) => (l, rewriteTyp emptySubst mono t)
            let newOutput := rewriteTyp emptySubst mono f.output
            let newBody := rewriteTypedTerm tds emptySubst mono f.body
            acc.insert key (.function
              { f with inputs := newInputs, output := newOutput, body := newBody })
          else acc
        | .dataType dt =>
          if dt.params.isEmpty then
            let newCtors := dt.constructors.map fun c =>
              { c with argTypes := c.argTypes.map (rewriteTyp emptySubst mono) }
            acc.insert key (.dataType { dt with constructors := newCtors })
          else acc
        | .constructor dt c =>
          if dt.params.isEmpty then
            let newArgTypes := c.argTypes.map (rewriteTyp emptySubst mono)
            let newCtor : Constructor := { c with argTypes := newArgTypes }
            let rewrittenCtors := dt.constructors.map fun c' =>
              { c' with argTypes := c'.argTypes.map (rewriteTyp emptySubst mono) }
            let newDt : DataType := { dt with constructors := rewrittenCtors }
            acc.insert key (.constructor newDt newCtor)
          else acc)
      default
    ∃ dt, fromSource.getByKey g = some (.dataType dt) := by
  intro emptySubst fromSource
  have hmem_g : (g, Typed.Declaration.dataType dt_tds) ∈ tds.pairs.toList :=
    IndexMap.mem_pairs_of_getByKey _ _ _ hget_g
  obtain ⟨gIdx, hgIdx_lt, hgIdx_eq⟩ := List.getElem_of_mem hmem_g
  rw [Array.length_toList] at hgIdx_lt
  have hgIdx_eq' : tds.pairs[gIdx]'hgIdx_lt = (g, Typed.Declaration.dataType dt_tds) := by
    rw [← hgIdx_eq, Array.getElem_toList]
  let Motive : Nat → Typed.Decls → Prop := fun i acc =>
    (i ≤ gIdx ∧ acc.getByKey g = none) ∨
    (gIdx < i ∧ ∃ dt, acc.getByKey g = some (.dataType dt))
  have hinit : Motive 0 (default : Typed.Decls) :=
    Or.inl ⟨Nat.zero_le _, default_typedDecls_getByKey_none g⟩
  have hfold : Motive tds.pairs.size fromSource := Array.foldl_induction
    (motive := Motive) hinit
    (by
      intro i acc hM
      have hp_mem : tds.pairs[i.val]'i.isLt ∈ tds.pairs.toList :=
        Array.mem_toList_iff.mpr (Array.getElem_mem _)
      have h_if_gkey :
          ∀ (p : Global × Typed.Declaration),
            p = tds.pairs[i.val]'i.isLt → (p.1 == g) = true →
            p = (g, .dataType dt_tds) ∧ i.val = gIdx := by
        intro p hp_eq hkey
        refine ⟨?_, ?_⟩
        · have hp_in : p ∈ tds.pairs.toList := by rw [hp_eq]; exact hp_mem
          exact indexMap_pairs_key_unique _ hp_in hmem_g hkey
        · have hi_full : i.val < tds.pairs.toList.length := by
            rw [Array.length_toList]; exact i.isLt
          have hp_list : tds.pairs.toList[i.val]'hi_full = p := by
            rw [Array.getElem_toList]; exact hp_eq.symm
          have hg_full : gIdx < tds.pairs.toList.length := by
            rw [Array.length_toList]; exact hgIdx_lt
          have hg_list :
              tds.pairs.toList[gIdx]'hg_full = (g, Typed.Declaration.dataType dt_tds) := by
            rw [Array.getElem_toList]; exact hgIdx_eq'
          have hk_cmp :
              ((tds.pairs.toList[i.val]'hi_full).1 ==
                (tds.pairs.toList[gIdx]'hg_full).1) = true := by
            rw [hp_list, hg_list]; exact hkey
          exact indexMap_pairs_index_unique_of_key _ hi_full hg_full hk_cmp
      generalize hpr : tds.pairs[i.val]'i.isLt = p
      have h_if_gkey' : (p.1 == g) = true → p = (g, .dataType dt_tds) ∧ i.val = gIdx :=
        fun hk => h_if_gkey p hpr.symm hk
      have h_if_ne' : (p.1 == g) = false → i.val ≠ gIdx := by
        intro hne heq
        subst heq
        rw [hgIdx_eq'] at hpr
        subst hpr
        simp only [beq_self_eq_true] at hne
        cases hne
      obtain ⟨key, d⟩ := p
      cases d with
      | function f =>
        by_cases hfp : f.params.isEmpty = true
        · simp only [hfp, if_true]
          have hne : (key == g) = false := by
            by_cases hkg : (key == g) = true
            · exfalso
              have ⟨hpair, _⟩ := h_if_gkey' hkg
              cases hpair
            · exact Bool.not_eq_true _ |>.mp hkg
          have hi_ne : i.val ≠ gIdx := h_if_ne' hne
          rcases hM with ⟨hi_le, hn⟩ | ⟨hi_lt, hd_dt⟩
          · left
            refine ⟨by omega, ?_⟩
            rw [IndexMap.getByKey_insert_of_beq_false _ _ hne]; exact hn
          · right
            refine ⟨Nat.lt_succ_of_lt hi_lt, ?_⟩
            obtain ⟨dt', hdt'⟩ := hd_dt
            refine ⟨dt', ?_⟩
            rw [IndexMap.getByKey_insert_of_beq_false _ _ hne]; exact hdt'
        · have hfp' : f.params.isEmpty = false := Bool.not_eq_true _ |>.mp hfp
          simp only [hfp']
          have hne_key : (key == g) = false := by
            by_cases hkg : (key == g) = true
            · exfalso
              have ⟨hpair, _⟩ := h_if_gkey' hkg
              cases hpair
            · exact Bool.not_eq_true _ |>.mp hkg
          have hi_ne : i.val ≠ gIdx := h_if_ne' hne_key
          rcases hM with ⟨hi_le, hn⟩ | ⟨hi_lt, hd_dt⟩
          · left; exact ⟨by omega, hn⟩
          · right; exact ⟨Nat.lt_succ_of_lt hi_lt, hd_dt⟩
      | dataType dt =>
        by_cases hdp : dt.params.isEmpty = true
        · simp only [hdp, if_true]
          by_cases hkg : (key == g) = true
          · have hkeq : key = g := LawfulBEq.eq_of_beq hkg
            subst hkeq
            have ⟨hpair, hi_eq⟩ := h_if_gkey' (by simp)
            injection hpair with _ hdSnd
            injection hdSnd with hdt_eq
            subst hdt_eq
            right
            refine ⟨by omega, ?_⟩
            exact ⟨_, IndexMap.getByKey_insert_self _ _ _⟩
          · have hne : (key == g) = false := Bool.not_eq_true _ |>.mp hkg
            have hi_ne : i.val ≠ gIdx := h_if_ne' hne
            rcases hM with ⟨hi_le, hn⟩ | ⟨hi_lt, hd_dt⟩
            · left
              refine ⟨by omega, ?_⟩
              rw [IndexMap.getByKey_insert_of_beq_false _ _ hne]; exact hn
            · right
              refine ⟨Nat.lt_succ_of_lt hi_lt, ?_⟩
              obtain ⟨dt', hdt'⟩ := hd_dt
              refine ⟨dt', ?_⟩
              rw [IndexMap.getByKey_insert_of_beq_false _ _ hne]; exact hdt'
        · have hdp' : dt.params.isEmpty = false := Bool.not_eq_true _ |>.mp hdp
          simp only [hdp']
          have hne : (key == g) = false := by
            by_cases hkg : (key == g) = true
            · exfalso
              have hkeq : key = g := LawfulBEq.eq_of_beq hkg
              subst hkeq
              have ⟨hpair, _⟩ := h_if_gkey' (by simp)
              injection hpair with _ hdSnd
              injection hdSnd with hdt_eq
              subst hdt_eq
              rw [hparams] at hdp'
              simp at hdp'
            · exact Bool.not_eq_true _ |>.mp hkg
          have hi_ne : i.val ≠ gIdx := h_if_ne' hne
          rcases hM with ⟨hi_le, hn⟩ | ⟨hi_lt, hd_dt⟩
          · left; exact ⟨by omega, hn⟩
          · right; exact ⟨Nat.lt_succ_of_lt hi_lt, hd_dt⟩
      | constructor dtC c =>
        by_cases hcp : dtC.params.isEmpty = true
        · simp only [hcp, if_true]
          have hne : (key == g) = false := by
            by_cases hkg : (key == g) = true
            · exfalso
              have ⟨hpair, _⟩ := h_if_gkey' hkg
              cases hpair
            · exact Bool.not_eq_true _ |>.mp hkg
          have hi_ne : i.val ≠ gIdx := h_if_ne' hne
          rcases hM with ⟨hi_le, hn⟩ | ⟨hi_lt, hd_dt⟩
          · left
            refine ⟨by omega, ?_⟩
            rw [IndexMap.getByKey_insert_of_beq_false _ _ hne]; exact hn
          · right
            refine ⟨Nat.lt_succ_of_lt hi_lt, ?_⟩
            obtain ⟨dt', hdt'⟩ := hd_dt
            refine ⟨dt', ?_⟩
            rw [IndexMap.getByKey_insert_of_beq_false _ _ hne]; exact hdt'
        · have hcp' : dtC.params.isEmpty = false := Bool.not_eq_true _ |>.mp hcp
          simp only [hcp']
          have hne : (key == g) = false := by
            by_cases hkg : (key == g) = true
            · exfalso
              have ⟨hpair, _⟩ := h_if_gkey' hkg
              cases hpair
            · exact Bool.not_eq_true _ |>.mp hkg
          have hi_ne : i.val ≠ gIdx := h_if_ne' hne
          rcases hM with ⟨hi_le, hn⟩ | ⟨hi_lt, hd_dt⟩
          · left; exact ⟨by omega, hn⟩
          · right; exact ⟨Nat.lt_succ_of_lt hi_lt, hd_dt⟩)
  rcases hfold with ⟨hi_le, _⟩ | ⟨_, hdt⟩
  · exfalso; omega
  · exact hdt

/-- **L2 Phase 2** (`withNewDts` fold): preserves the `.dataType` shape at key `g`. -/
theorem L2_phase2_withNewDts
    (tds : Typed.Decls) (mono : MonoMap)
    (newDataTypes : Array DataType)
    (hNewDtBridge : NewDtBridge tds newDataTypes)
    (hDtNameIsKey : ∀ (key : Global) (dt : DataType),
      (key, Typed.Declaration.dataType dt) ∈ tds.pairs.toList → key = dt.name)
    (hCtorPresent : ∀ (dtkey : Global) (dt : DataType) (c : Constructor),
      (dtkey, Typed.Declaration.dataType dt) ∈ tds.pairs.toList →
      c ∈ dt.constructors →
      ∃ cc, (dt.name.pushNamespace c.nameHead,
        Typed.Declaration.constructor dt cc) ∈ tds.pairs.toList)
    {g : Global} {dt_tds : DataType}
    (hget_g : tds.getByKey g = some (.dataType dt_tds))
    (init : Typed.Decls)
    (hinit : ∃ dt, init.getByKey g = some (.dataType dt)) :
    let emptySubst : Global → Option Typ := fun _ => none
    ∃ dt, (newDataTypes.foldl
      (fun acc dt =>
        let rewrittenCtors := dt.constructors.map fun c =>
          { c with argTypes := c.argTypes.map (rewriteTyp emptySubst mono) }
        let newDt : DataType := { dt with constructors := rewrittenCtors }
        let acc' := acc.insert dt.name (.dataType newDt)
        rewrittenCtors.foldl
          (fun acc'' c =>
            let cName := dt.name.pushNamespace c.nameHead
            acc''.insert cName (.constructor newDt c))
          acc')
      init).getByKey g = some (.dataType dt) := by
  intro emptySubst
  have hmem_g : (g, Typed.Declaration.dataType dt_tds) ∈ tds.pairs.toList :=
    IndexMap.mem_pairs_of_getByKey _ _ _ hget_g
  let P : Typed.Decls → Prop := fun acc =>
    ∃ dt, acc.getByKey g = some (.dataType dt)
  apply Array.foldl_induction (motive := fun _ acc => P acc) hinit
  intro i acc hP
  let dtOuter := newDataTypes[i.val]'i.isLt
  have hdtOuter_mem : dtOuter ∈ newDataTypes := Array.getElem_mem _
  obtain ⟨gSrc, orig, hget_gSrc, hname_eq, hhead_eq⟩ :=
    hNewDtBridge dtOuter hdtOuter_mem
  let rewrittenCtors : List Constructor :=
    dtOuter.constructors.map fun c =>
      ({ c with argTypes := c.argTypes.map (rewriteTyp emptySubst mono) } : Constructor)
  have hctor_fold_preserves :
      ∀ (cs : List Constructor) (newDt : DataType) (init' : Typed.Decls),
        (∀ c ∈ cs, dtOuter.name.pushNamespace c.nameHead ≠ g) →
        P init' →
        P (cs.foldl
          (fun acc'' c =>
            let cName := dtOuter.name.pushNamespace c.nameHead
            acc''.insert cName (.constructor newDt c))
          init') := by
    intro cs newDt init'
    induction cs generalizing init' with
    | nil => intro _ hP'; exact hP'
    | cons c rest ih =>
      intro hne_all hP'
      simp only [List.foldl_cons]
      have hne_c : dtOuter.name.pushNamespace c.nameHead ≠ g :=
        hne_all c List.mem_cons_self
      have hne_beq : (dtOuter.name.pushNamespace c.nameHead == g) = false := by
        cases hbeq : (dtOuter.name.pushNamespace c.nameHead == g) with
        | true => exact absurd (LawfulBEq.eq_of_beq hbeq) hne_c
        | false => rfl
      have hP_head :
          P (init'.insert (dtOuter.name.pushNamespace c.nameHead) (.constructor newDt c)) := by
        obtain ⟨dt', hdt'⟩ := hP'
        exact ⟨dt', by rw [IndexMap.getByKey_insert_of_beq_false _ _ hne_beq]; exact hdt'⟩
      exact ih _ (fun c' hc' => hne_all c' (List.mem_cons_of_mem _ hc')) hP_head
  have hne_all : ∀ c ∈ rewrittenCtors,
      dtOuter.name.pushNamespace c.nameHead ≠ g := by
    intro c hc_mem
    have hc_head_in : c.nameHead ∈ dtOuter.constructors.map (·.nameHead) := by
      simp only [rewrittenCtors, List.mem_map] at hc_mem
      obtain ⟨c', hc'_mem, hc'_eq⟩ := hc_mem
      refine List.mem_map.mpr ⟨c', hc'_mem, ?_⟩
      rw [← hc'_eq]
    rw [hhead_eq] at hc_head_in
    rw [List.mem_map] at hc_head_in
    obtain ⟨cOrig, hcOrig_mem, hcOrig_eq⟩ := hc_head_in
    have hmem_dtSrc : (gSrc, Typed.Declaration.dataType orig) ∈ tds.pairs.toList :=
      IndexMap.mem_pairs_of_getByKey _ _ _ hget_gSrc
    have hgSrc_name : gSrc = orig.name := hDtNameIsKey gSrc orig hmem_dtSrc
    obtain ⟨cc, hcc_mem⟩ := hCtorPresent gSrc orig cOrig hmem_dtSrc hcOrig_mem
    intro hfalse
    have hkey_eq : orig.name.pushNamespace cOrig.nameHead =
        dtOuter.name.pushNamespace c.nameHead := by
      rw [hname_eq, hgSrc_name, hcOrig_eq]
    have hcc_mem_at_g :
        (g, Typed.Declaration.constructor orig cc) ∈ tds.pairs.toList := by
      rw [← hfalse, ← hkey_eq]; exact hcc_mem
    have hclash := indexMap_pairs_key_unique _ hcc_mem_at_g hmem_g (by simp)
    cases hclash
  show P _
  let dt := dtOuter
  let rewrittenCtors' := rewrittenCtors
  let newDt : DataType := { dt with constructors := rewrittenCtors' }
  let acc' := acc.insert dt.name (.dataType newDt)
  have hP_acc' : P acc' := by
    by_cases hname : (dt.name == g) = true
    · have hname_eq' : dt.name = g := LawfulBEq.eq_of_beq hname
      refine ⟨newDt, ?_⟩
      show (acc.insert dt.name (.dataType newDt)).getByKey g = some (.dataType newDt)
      rw [hname_eq']
      exact IndexMap.getByKey_insert_self _ _ _
    · have hne : (dt.name == g) = false := Bool.not_eq_true _ |>.mp hname
      obtain ⟨dt', hdt'⟩ := hP
      refine ⟨dt', ?_⟩
      show (acc.insert dt.name (.dataType newDt)).getByKey g = _
      rw [IndexMap.getByKey_insert_of_beq_false _ _ hne]
      exact hdt'
  exact hctor_fold_preserves rewrittenCtors' newDt acc' hne_all hP_acc'

/-- **L2 Phase 3** (`newFunctions` fold): preserves the `.dataType` shape at key `g`. -/
theorem L2_phase3_newFunctions
    (tds : Typed.Decls) (mono : MonoMap)
    (newFunctions : Array Typed.Function)
    (hNewFnBridge : NewFnBridge tds newFunctions)
    {g : Global} {dt_tds : DataType}
    (hget_g : tds.getByKey g = some (.dataType dt_tds))
    (init : Typed.Decls)
    (hinit : ∃ dt, init.getByKey g = some (.dataType dt)) :
    let emptySubst : Global → Option Typ := fun _ => none
    ∃ dt, (newFunctions.foldl
      (fun acc f =>
        let newInputs := f.inputs.map fun (l, t) => (l, rewriteTyp emptySubst mono t)
        let newOutput := rewriteTyp emptySubst mono f.output
        let newBody := rewriteTypedTerm tds emptySubst mono f.body
        let newF : Typed.Function :=
          { f with inputs := newInputs, output := newOutput, body := newBody }
        acc.insert f.name (.function newF))
      init).getByKey g = some (.dataType dt) := by
  intro emptySubst
  let P : Typed.Decls → Prop := fun acc =>
    ∃ dt, acc.getByKey g = some (.dataType dt)
  apply Array.foldl_induction (motive := fun _ acc => P acc) hinit
  intro i acc hP
  let f := newFunctions[i.val]'i.isLt
  have hf_mem : f ∈ newFunctions := Array.getElem_mem _
  obtain ⟨gFn, orig_f, hget_gFn, hf_name⟩ := hNewFnBridge f hf_mem
  have hne : (f.name == g) = false := by
    by_cases hkg : (f.name == g) = true
    · exfalso
      have hfeq : f.name = g := LawfulBEq.eq_of_beq hkg
      rw [hf_name] at hfeq
      rw [hfeq] at hget_gFn
      rw [hget_g] at hget_gFn
      cases hget_gFn
    · exact Bool.not_eq_true _ |>.mp hkg
  obtain ⟨dt', hdt'⟩ := hP
  show P _
  refine ⟨dt', ?_⟩
  show (acc.insert f.name _).getByKey g = some (.dataType dt')
  rw [IndexMap.getByKey_insert_of_beq_false _ _ hne]
  exact hdt'

/-- **L2**: every `.dataType` key in `tds` yields a `.dataType` key in `cd`.

**Strengthened signature** (ported from `L2Scratch.lean` on 2026-04-23): takes
`hdt_params_empty`, `hCtorPresent`, `hDtNameIsKey`, `hNewDtBridge`,
`hNewFnBridge` as explicit hypotheses. Their discharge (via
`typedDecls_dt_params_empty_of_fullyMonomorphic`,
`checkAndSimplify_preserves_ctorPresent`, `checkAndSimplify_preserves_dtNameIsKey`,
`newDtBridge_derive`, `newFnBridge_derive`) lives in `CheckSound` +
`CompilerProgress` (downstream); callers supply them directly. -/
theorem L2_tds_dtkey_survives_to_cd
    {tds : Typed.Decls} {cd : Concrete.Decls}
    (hconc : tds.concretize = .ok cd)
    (hdt_params_empty : ∀ g dt, tds.getByKey g = some (.dataType dt) → dt.params = [])
    (hCtorPresent : ∀ (dtkey : Global) (dt : DataType) (c : Constructor),
      (dtkey, Typed.Declaration.dataType dt) ∈ tds.pairs.toList →
      c ∈ dt.constructors →
      ∃ cc, (dt.name.pushNamespace c.nameHead,
        Typed.Declaration.constructor dt cc) ∈ tds.pairs.toList)
    (hDtNameIsKey : ∀ (key : Global) (dt : DataType),
      (key, Typed.Declaration.dataType dt) ∈ tds.pairs.toList → key = dt.name)
    (hNewDtBridge : ∀ {drained : DrainState},
      concretizeDrain tds (concretizeDrainFuel tds)
          { pending := concretizeSeed tds, seen := {}, mono := {},
            newFunctions := #[], newDataTypes := #[] } = .ok drained →
      NewDtBridge tds drained.newDataTypes)
    (hNewFnBridge : ∀ {drained : DrainState},
      concretizeDrain tds (concretizeDrainFuel tds)
          { pending := concretizeSeed tds, seen := {}, mono := {},
            newFunctions := #[], newDataTypes := #[] } = .ok drained →
      NewFnBridge tds drained.newFunctions) :
    ∀ g dt_tds, tds.getByKey g = some (.dataType dt_tds) →
      ∃ dt_cd, cd.getByKey g = some (.dataType dt_cd) := by
  intro g dt_tds hget_tds
  unfold Typed.Decls.concretize at hconc
  simp only [bind, Except.bind] at hconc
  split at hconc
  · contradiction
  rename_i drained _hdrain
  let monoDecls : Typed.Decls :=
    concretizeBuild tds drained.mono drained.newFunctions drained.newDataTypes
  have hNewDt := hNewDtBridge _hdrain
  have hNewFn := hNewFnBridge _hdrain
  have hparams : dt_tds.params = [] := hdt_params_empty g dt_tds hget_tds
  have hP1 := L2_phase1_fromSource tds drained.mono hget_tds hparams
  have hP2 := L2_phase2_withNewDts tds drained.mono drained.newDataTypes
    hNewDt hDtNameIsKey hCtorPresent hget_tds _ hP1
  have hP3 := L2_phase3_newFunctions tds drained.mono drained.newFunctions
    hNewFn hget_tds _ hP2
  have hmono : ∃ dt, monoDecls.getByKey g = some (.dataType dt) := by
    show ∃ dt, (concretizeBuild tds drained.mono drained.newFunctions drained.newDataTypes).getByKey g = _
    unfold concretizeBuild
    exact hP3
  obtain ⟨dt_mono, hget_mono⟩ := hmono
  have hshape := step4Lower_fold_kind_at_key hget_mono hconc
  simp only at hshape
  exact hshape

/-! #### L3: cd-side `.ref` targets trace to tds-side `.ref` targets.

L3 states the bridge directly: every `.ref g'` appearing in any `cd` declaration
type has `g'` bound to a `.dataType` in `tds`. This collapses L3 + L1 into the
single predicate `RefTargetsInTds` on the concrete side. -/

/-- `.ref g'` in a cd type: each bound `g'` is a tds-dt-key. -/
inductive RefTargetsInTds (tds : Typed.Decls) : Concrete.Typ → Prop
  | unit    : RefTargetsInTds tds .unit
  | field   : RefTargetsInTds tds .field
  | pointer {inner} (h : RefTargetsInTds tds inner) : RefTargetsInTds tds (.pointer inner)
  | function {ins out} : RefTargetsInTds tds (.function ins out)
  | tuple {ts} (h : ∀ t ∈ ts.toList, RefTargetsInTds tds t) :
      RefTargetsInTds tds (.tuple ts)
  | array {t n} (h : RefTargetsInTds tds t) : RefTargetsInTds tds (.array t n)
  | ref {g} (hdt : ∃ dt_tds, tds.getByKey g = some (.dataType dt_tds)) :
      RefTargetsInTds tds (.ref g)

def AllRefsTargetTds (cd : Concrete.Decls) (tds : Typed.Decls) : Prop :=
  ∀ name d, cd.getByKey name = some d →
    match d with
    | .function f =>
        (∀ lt ∈ f.inputs, RefTargetsInTds tds lt.snd) ∧
        RefTargetsInTds tds f.output
    | .dataType dt =>
        ∀ c ∈ dt.constructors, ∀ t ∈ c.argTypes, RefTargetsInTds tds t
    | .constructor _ c =>
        ∀ t ∈ c.argTypes, RefTargetsInTds tds t

/-! **L3 body helpers** (decomposition).

(1) predicate `TypNoAppRefDtKey tds t` — structural typed-side invariant
    forbidding `.app` + requiring every `.ref g'` to target a tds dt-key;
(2) `typToConcrete`-preservation of `RefTargetsInTds`;
(3) step4Lower and its fold both preserve `AllRefsTargetTds`;
(4) single sub-sorry `monoDecls_types_noAppRefDtKey` establishes the
    predicate on `monoDecls`. -/

/-- `.app`-free typed type that additionally has all `.ref g'` targeting tds
dt-keys. Combines the `TypRefsAreDtKeys`-style `.ref` obligation with a hard
exclusion of the `.app` constructor. -/
inductive TypNoAppRefDtKey (tds : Typed.Decls) : Typ → Prop
  | unit    : TypNoAppRefDtKey tds .unit
  | field   : TypNoAppRefDtKey tds .field
  | mvar n  : TypNoAppRefDtKey tds (.mvar n)
  | pointer {inner} (h : TypNoAppRefDtKey tds inner) :
      TypNoAppRefDtKey tds (.pointer inner)
  | function {ins out}
      (hi : ∀ t ∈ ins, TypNoAppRefDtKey tds t)
      (ho : TypNoAppRefDtKey tds out) :
      TypNoAppRefDtKey tds (.function ins out)
  | tuple {ts} (h : ∀ t ∈ ts.toList, TypNoAppRefDtKey tds t) :
      TypNoAppRefDtKey tds (.tuple ts)
  | array {t n} (h : TypNoAppRefDtKey tds t) :
      TypNoAppRefDtKey tds (.array t n)
  | ref {g} (hdt : ∃ dt, tds.getByKey g = some (.dataType dt)) :
      TypNoAppRefDtKey tds (.ref g)

/-- Declaration-wise statement: every type anywhere in `d`'s annotations
satisfies `TypNoAppRefDtKey tds`. Parallels `AllRefsAreDtKeys` and
`AllRefsTargetTds` per-entry schema. -/
def declTypesNoAppRefDtKey (tds : Typed.Decls) : Typed.Declaration → Prop
  | .function f =>
      (∀ lt ∈ f.inputs, TypNoAppRefDtKey tds lt.snd) ∧
      TypNoAppRefDtKey tds f.output
  | .dataType dt =>
      ∀ c ∈ dt.constructors, ∀ t ∈ c.argTypes, TypNoAppRefDtKey tds t
  | .constructor _ c =>
      ∀ t ∈ c.argTypes, TypNoAppRefDtKey tds t

/-- Structural preservation: `typToConcrete mono t_typed = .ok t_cd` with
`t_typed` satisfying `TypNoAppRefDtKey tds` ⇒ `RefTargetsInTds tds t_cd`.

Does NOT require `mono` info because `.app` is forbidden and `.ref g` maps
literally to `.ref g`. Proved by induction on the `TypNoAppRefDtKey` predicate. -/
theorem typToConcrete_preserves_RefTargetsInTds
    {mono : Std.HashMap (Global × Array Typ) Global} {tds : Typed.Decls}
    {t_typed : Typ} (hP : TypNoAppRefDtKey tds t_typed) :
    ∀ {t_cd : Concrete.Typ}, typToConcrete mono t_typed = .ok t_cd →
      RefTargetsInTds tds t_cd := by
  induction hP with
  | unit =>
    intro t_cd htc
    simp only [typToConcrete, pure, Except.pure] at htc
    cases htc; exact .unit
  | field =>
    intro t_cd htc
    simp only [typToConcrete, pure, Except.pure] at htc
    cases htc; exact .field
  | mvar =>
    intro t_cd htc
    simp only [typToConcrete] at htc
    cases htc
  | pointer _ ih =>
    intro t_cd htc
    simp only [typToConcrete, bind, Except.bind, pure, Except.pure] at htc
    split at htc
    · cases htc
    rename_i t' hinner
    simp only [Except.ok.injEq] at htc
    cases htc
    exact .pointer (ih hinner)
  | array _ ih =>
    intro t_cd htc
    simp only [typToConcrete, bind, Except.bind, pure, Except.pure] at htc
    split at htc
    · cases htc
    rename_i t' hinner
    simp only [Except.ok.injEq] at htc
    cases htc
    exact .array (ih hinner)
  | ref hdt =>
    intro t_cd htc
    simp only [typToConcrete, pure, Except.pure] at htc
    cases htc
    exact .ref hdt
  | @tuple ts hin ih =>
    intro t_cd htc
    simp only [typToConcrete, bind, Except.bind, pure, Except.pure] at htc
    split at htc
    · cases htc
    rename_i ts' hmap
    simp only [Except.ok.injEq] at htc
    cases htc
    refine .tuple ?_
    -- Bridge the attach-form mapM into a plain ts.mapM via subtype rewrite.
    have hmap' : ts.mapM (fun t => typToConcrete mono t) = .ok ts' := by
      rw [Array.mapM_subtype (g := fun t => typToConcrete mono t) (fun _ _ => rfl)] at hmap
      rw [Array.unattach_attach] at hmap
      exact hmap
    intro t_cd_elem ht_cd_mem_list
    have ht_cd_mem : t_cd_elem ∈ ts' :=
      Array.mem_toList_iff.mp ht_cd_mem_list
    refine Array.mem_mapM_ok_forall
      (P := fun x => x ∈ ts)
      (Q := fun tc => RefTargetsInTds tds tc)
      ?_ ts ts' (fun x hx => hx) hmap' t_cd_elem ht_cd_mem
    intro x hxMem fx hfx
    exact ih x (Array.mem_toList_iff.mpr hxMem) hfx
  | @function ins out _ _ _ _ =>
    intro t_cd htc
    simp only [typToConcrete, bind, Except.bind, pure, Except.pure] at htc
    split at htc
    · cases htc
    split at htc
    · cases htc
    rename_i out' hout' ins' hins'
    simp only [Except.ok.injEq] at htc
    cases htc
    -- `RefTargetsInTds.function` has no hypotheses.
    exact .function

/-- Variant of `AppRefToDt` for monoDecls (post-rewriteTyp) types. Allows
`.ref g` to point to EITHER a tds dt-key OR a drained `newDataTypes` name.
`.app g args` retains the tds dt-key requirement (polymorphic source dts). -/
inductive Typed.Typ.AppRefToDtOrNewDt (tds : Typed.Decls)
    (newDataTypes : Array DataType) : Typ → Prop
  | unit : AppRefToDtOrNewDt tds newDataTypes .unit
  | field : AppRefToDtOrNewDt tds newDataTypes .field
  | mvar (n) : AppRefToDtOrNewDt tds newDataTypes (.mvar n)
  | ref {g}
      (hdt : (∃ dt, tds.getByKey g = some (.dataType dt) ∧ dt.params = []) ∨
             (∃ newDt ∈ newDataTypes, newDt.name = g)) :
      AppRefToDtOrNewDt tds newDataTypes (.ref g)
  | app {g args}
      (hdt : ∃ dt, tds.getByKey g = some (.dataType dt))
      (hargs : ∀ t ∈ args, AppRefToDtOrNewDt tds newDataTypes t) :
      AppRefToDtOrNewDt tds newDataTypes (.app g args)
  | tuple {ts} (h : ∀ t ∈ ts, AppRefToDtOrNewDt tds newDataTypes t) :
      AppRefToDtOrNewDt tds newDataTypes (.tuple ts)
  | array {t n} (h : AppRefToDtOrNewDt tds newDataTypes t) :
      AppRefToDtOrNewDt tds newDataTypes (.array t n)
  | pointer {t} (h : AppRefToDtOrNewDt tds newDataTypes t) :
      AppRefToDtOrNewDt tds newDataTypes (.pointer t)
  | function {ins out}
      (h_ins : ∀ t ∈ ins, AppRefToDtOrNewDt tds newDataTypes t)
      (h_out : AppRefToDtOrNewDt tds newDataTypes out) :
      AppRefToDtOrNewDt tds newDataTypes (.function ins out)

/-- Lift `SrcTypRefsAreDtKeys` (source-side) to typed-side `AppRefToDt`
under key/dt presence preservation. The `.ref` arm requires `params = []`
preservation; the `.refTypeParam` arm passes through (same param list);
the `.app` arm only requires dt-presence (typed-side is polymorphism-
friendly). -/
theorem AppRefToDt_of_SrcTypRefsAreDtKeys
    {decls : Source.Decls} {tds : Typed.Decls} {params : List String}
    (h_dt_lift : ∀ g, (∃ dt_src, decls.getByKey g = some (.dataType dt_src)) →
      ∃ dt_td, tds.getByKey g = some (.dataType dt_td))
    (h_dt_params_lift : ∀ g,
      (∃ dt_src, decls.getByKey g = some (.dataType dt_src) ∧ dt_src.params = []) →
      ∃ dt_td, tds.getByKey g = some (.dataType dt_td) ∧ dt_td.params = [])
    {τ : Typ} (h : SrcTypRefsAreDtKeys decls params τ) :
    Typed.Typ.AppRefToDt tds params τ := by
  induction h with
  | unit => exact .unit
  | field => exact .field
  | mvar n => exact .mvar n
  | func _ _ ih_ins ih_out =>
    refine .function ?_ ih_out
    intro t ht
    exact ih_ins t ht
  | pointer _ ih => exact .pointer ih
  | tuple _ ih =>
    refine .tuple ?_
    intro t ht
    exact ih t (Array.mem_toList_iff.mpr ht)
  | array _ ih => exact .array ih
  | @ref g hdt => exact .ref (h_dt_params_lift g hdt)
  | @refTypeParam g hin => exact .refTypeParam hin
  | @app g args hdt _ ih =>
    obtain ⟨dt_src, hget, _hsize⟩ := hdt
    refine .app (h_dt_lift g ⟨dt_src, hget⟩) ?_
    intro t ht
    exact ih t (Array.mem_toList_iff.mpr ht)

/-- `typToConcrete` produces `Concrete.Typ.RefClosed cd` under the cd-side
dt-presence premise: every dt-key target of `t_typed`'s `.ref/.app` resolves
to a `.dataType` in `cd`.

Two preconditions:
- `hAR : Typed.Typ.AppRefToDt tds t_typed` — supplies, for each `.ref g`/`.app g _`
  occurrence, that `g` is a tds dt-key.
- `hcdAt : ∀ g, (∃ dt, tds.getByKey g = some (.dataType dt)) →
            ∃ cdt, cd.getByKey g = some (.dataType cdt)` — tds dt-key ⇒ cd dt-key.
- `hcdMono : ∀ g args concName, mono[(g, args)]? = some concName →
            ∃ cdt, cd.getByKey concName = some (.dataType cdt)` — mono-image
  is cd dt-key.

`.app` arm (mono hit): typToConcrete maps to `.ref concName`, hcdMono closes.
`.app` arm (mono miss): typToConcrete maps to `.ref g`, hcdAt closes via hAR.
`.ref` arm: typToConcrete maps to `.ref g`, hcdAt closes via hAR. -/
theorem typToConcrete_RefClosed_via_StrongNewNameShape
    {cd : Concrete.Decls} {tds : Typed.Decls}
    {mono : Std.HashMap (Global × Array Typ) Global}
    (hcdAt : ∀ g, (∃ dt, tds.getByKey g = some (.dataType dt)) →
            ∃ cdt, cd.getByKey g = some (.dataType cdt))
    (hcdMono : ∀ (g : Global) (args : Array Typ) (concName : Global),
            mono[(g, args)]? = some concName →
            ∃ cdt, cd.getByKey concName = some (.dataType cdt))
    {t_typed : Typ} (hAR : Typed.Typ.AppRefToDt tds [] t_typed) :
    ∀ {t_cd : Concrete.Typ}, typToConcrete mono t_typed = .ok t_cd →
      Concrete.Typ.RefClosed cd t_cd := by
  induction hAR with
  | unit =>
    intro t_cd htc
    simp only [typToConcrete, pure, Except.pure] at htc
    cases htc; exact .unit
  | field =>
    intro t_cd htc
    simp only [typToConcrete, pure, Except.pure] at htc
    cases htc; exact .field
  | mvar n =>
    intro t_cd htc
    simp only [typToConcrete] at htc
    cases htc
  | @ref g hdt =>
    intro t_cd htc
    simp only [typToConcrete, pure, Except.pure] at htc
    cases htc
    obtain ⟨dt, hget, _⟩ := hdt
    exact .ref (hcdAt g ⟨dt, hget⟩)
  | @refTypeParam g hin =>
    -- params = [] ⇒ List.any [] is false; vacuous.
    intro _ _
    exact absurd hin (by simp)
  | @app g args hdt _ ih =>
    intro t_cd htc
    simp only [typToConcrete, bind, Except.bind, pure, Except.pure] at htc
    split at htc
    · -- mono hit: typToConcrete returns .ref concName; use hcdMono.
      rename_i concName hsome
      simp only [Except.ok.injEq] at htc
      cases htc
      exact .ref (hcdMono g args concName hsome)
    · -- mono miss: typToConcrete returns .ref g; use hcdAt.
      simp only [Except.ok.injEq] at htc
      cases htc
      exact .ref (hcdAt g hdt)
  | @tuple ts _ ih =>
    intro t_cd htc
    simp only [typToConcrete, bind, Except.bind, pure, Except.pure] at htc
    split at htc
    · cases htc
    rename_i ts' hmap
    simp only [Except.ok.injEq] at htc
    cases htc
    refine .tuple ?_
    have hmap' : ts.mapM (fun t => typToConcrete mono t) = .ok ts' := by
      rw [Array.mapM_subtype (g := fun t => typToConcrete mono t) (fun _ _ => rfl)] at hmap
      rw [Array.unattach_attach] at hmap
      exact hmap
    intro t_cd_elem ht_cd_mem_list
    have ht_cd_mem : t_cd_elem ∈ ts' :=
      Array.mem_toList_iff.mp ht_cd_mem_list
    refine Array.mem_mapM_ok_forall
      (P := fun x => x ∈ ts)
      (Q := fun tc => Concrete.Typ.RefClosed cd tc)
      ?_ ts ts' (fun x hx => hx) hmap' t_cd_elem ht_cd_mem
    intro x hxMem fx hfx
    exact ih x hxMem hfx
  | @array t n _ iht =>
    intro t_cd htc
    simp only [typToConcrete, bind, Except.bind, pure, Except.pure] at htc
    split at htc
    · cases htc
    rename_i t' hinner
    simp only [Except.ok.injEq] at htc
    cases htc
    exact .array (iht hinner)
  | @pointer t _ iht =>
    intro t_cd htc
    simp only [typToConcrete, bind, Except.bind, pure, Except.pure] at htc
    split at htc
    · cases htc
    rename_i t' hinner
    simp only [Except.ok.injEq] at htc
    cases htc
    exact .pointer (iht hinner)
  | @function ins out _ _ _ _ =>
    intro t_cd htc
    simp only [typToConcrete, bind, Except.bind, pure, Except.pure] at htc
    split at htc
    · cases htc
    split at htc
    · cases htc
    rename_i out' hout' ins' hins'
    simp only [Except.ok.injEq] at htc
    cases htc
    exact .function

/-- `rewriteTyp emptySubst drained.mono` on an `AppRefToDt tds`-typed input
produces an `AppRefToDtOrNewDt tds drained.newDataTypes` output. The mono-hit
case in `.app` produces `.ref concName` where `concName ∈ drained.newDataTypes`
via `MonoShapeOk`. -/
theorem rewriteTyp_preserves_AppRefToDtOrNewDt
    {tds : Typed.Decls} {drained : DrainState}
    (hMonoShape : drained.MonoShapeOk tds)
    {τ : Typ} (hAR : Typed.Typ.AppRefToDt tds [] τ) :
    RefClosedBody.Typed.Typ.AppRefToDtOrNewDt tds drained.newDataTypes
      (rewriteTyp (fun _ => none) drained.mono τ) := by
  induction hAR with
  | unit => unfold rewriteTyp; exact .unit
  | field => unfold rewriteTyp; exact .field
  | mvar n => unfold rewriteTyp; exact .mvar n
  | @ref g hdt =>
    unfold rewriteTyp
    simp only [Option.getD_none]
    exact .ref (Or.inl hdt)
  | @refTypeParam g hin =>
    -- params = [] ⇒ List.any [] is false; vacuous.
    exact absurd hin (by simp)
  | @app g args hdt _ ih =>
    unfold rewriteTyp
    simp only
    cases hsub : drained.mono[(g, args)]? with
    | none =>
      simp only [hsub]
      refine .app hdt ?_
      intro t' ht'
      obtain ⟨t0, ht0_mem, ht0_eq⟩ := mem_of_attach_map args _ ht'
      subst ht0_eq
      exact ih t0 ht0_mem
    | some concName =>
      simp only [hsub]
      obtain ⟨dt, hget⟩ := hdt
      obtain ⟨newDt, hnewDt_mem, hnewDt_name, _⟩ := hMonoShape g args concName hsub hget
      exact .ref (Or.inr ⟨newDt, hnewDt_mem, hnewDt_name⟩)
  | @tuple ts _ ih =>
    unfold rewriteTyp
    refine .tuple ?_
    intro t' ht'
    obtain ⟨t0, ht0_mem, ht0_eq⟩ := mem_of_attach_map ts _ ht'
    subst ht0_eq
    exact ih t0 ht0_mem
  | @array t n _ iht =>
    unfold rewriteTyp; exact .array iht
  | @pointer t _ iht =>
    unfold rewriteTyp; exact .pointer iht
  | @function ins out _ _ ih_ins ih_out =>
    unfold rewriteTyp
    refine .function ?_ ih_out
    intro t' ht'
    obtain ⟨t0, ht0_mem, ht0_eq⟩ := list_mem_of_attach_map ins _ ht'
    subst ht0_eq
    exact ih_ins t0 ht0_mem

/-- Predicate `Typ.containsApp g args t`: `t` syntactically contains an
`.app g args` subterm. Used by `typToConcrete_RefClosed_via_AppRefToDtOrNewDt`
to thread the mono-covers-reachable-apps obligation through the structural
induction.

Defined as an inductive Prop over `Typ` to avoid termination/decidability
quirks of recursive Prop-valued definitions. -/
inductive Typ.containsApp (g : Global) (args : Array Typ) : Typ → Prop
  | here : Typ.containsApp g args (.app g args)
  | underAppArg {g0 args0 t} (hmem : t ∈ args0)
      (h : Typ.containsApp g args t) :
      Typ.containsApp g args (.app g0 args0)
  | underTupleElt {ts t} (hmem : t ∈ ts) (h : Typ.containsApp g args t) :
      Typ.containsApp g args (.tuple ts)
  | underArray {t n} (h : Typ.containsApp g args t) :
      Typ.containsApp g args (.array t n)
  | underPointer {t} (h : Typ.containsApp g args t) :
      Typ.containsApp g args (.pointer t)
  | underFunctionIn {ins out t} (hmem : t ∈ ins)
      (h : Typ.containsApp g args t) :
      Typ.containsApp g args (.function ins out)
  | underFunctionOut {ins out} (h : Typ.containsApp g args out) :
      Typ.containsApp g args (.function ins out)

/-- Variant of `typToConcrete_RefClosed_via_StrongNewNameShape` that takes
`AppRefToDtOrNewDt tds newDataTypes` (suitable for monoDecls post-rewriteTyp
types). Discharge premises (tightened 2026-04-30 per Plan-agent audit):
- `hcdAt_tds`: tds dt-key g ⇒ cd dt-key g.
- `hcdAt_newDt`: drained newDt name g ⇒ cd dt-key g.
- `hcdMono_dt`: drained.mono image of a TDS DT-KEY ⇒ cd dt-key. (Mono may
  contain fn entries too; those are not exercised by this helper since the
  `.app` arm of `AppRefToDtOrNewDt` requires g to be a tds dt-key.)
- `hAppCovered`: every `.app g args` reachable in `t_typed` has an entry in
  `mono`. This rules out the mono-miss arm of `typToConcrete .app`, which
  would otherwise produce `.ref g` for a polymorphic `g` (not present in `cd`).
  Caller-side discharge: `t_typed` was produced by `rewriteTyp drained.mono`
  on a `Typed.Typ.AppRefToDt`-safe input, AND drain-completeness ensures
  `drained.mono` covers every reachable `.app`. The umbrella supplies this
  via `appsResolved_after_rewriteTyp` (a single SHARED bridging lemma; see
  its `BLOCKED-drain-app-completeness` note for the closure path). -/
theorem typToConcrete_RefClosed_via_AppRefToDtOrNewDt
    {cd : Concrete.Decls} {tds : Typed.Decls}
    {newDataTypes : Array DataType}
    {mono : Std.HashMap (Global × Array Typ) Global}
    (hcdAt_tds : ∀ g, (∃ dt, tds.getByKey g = some (.dataType dt) ∧ dt.params = []) →
            ∃ cdt, cd.getByKey g = some (.dataType cdt))
    (hcdAt_newDt : ∀ g, (∃ newDt ∈ newDataTypes, newDt.name = g) →
            ∃ cdt, cd.getByKey g = some (.dataType cdt))
    (hcdMono_dt : ∀ (g : Global) (args : Array Typ) (concName : Global),
            (∃ dt, tds.getByKey g = some (.dataType dt)) →
            mono[(g, args)]? = some concName →
            ∃ cdt, cd.getByKey concName = some (.dataType cdt))
    {t_typed : Typ}
    (hAR : Typed.Typ.AppRefToDtOrNewDt tds newDataTypes t_typed)
    (hAppCovered : ∀ g args, Typ.containsApp g args t_typed →
            ∃ concName, mono[(g, args)]? = some concName) :
    ∀ {t_cd : Concrete.Typ}, typToConcrete mono t_typed = .ok t_cd →
      Concrete.Typ.RefClosed cd t_cd := by
  -- Revert hAppCovered so the induction principle picks it up parameterized
  -- by the inducted-on type, threading mono coverage to sub-types.
  revert hAppCovered
  induction hAR with
  | unit =>
    intro _ t_cd htc
    simp only [typToConcrete, pure, Except.pure] at htc
    cases htc; exact .unit
  | field =>
    intro _ t_cd htc
    simp only [typToConcrete, pure, Except.pure] at htc
    cases htc; exact .field
  | mvar n =>
    intro _ t_cd htc
    simp only [typToConcrete] at htc
    cases htc
  | @ref g hdt =>
    intro _ t_cd htc
    simp only [typToConcrete, pure, Except.pure] at htc
    cases htc
    rcases hdt with hdt_tds | hdt_new
    · exact .ref (hcdAt_tds g hdt_tds)
    · exact .ref (hcdAt_newDt g hdt_new)
  | @app g args hdt _ ih =>
    intro hAppCovered t_cd htc
    simp only [typToConcrete, bind, Except.bind, pure, Except.pure] at htc
    split at htc
    · rename_i concName hsome
      simp only [Except.ok.injEq] at htc
      cases htc
      exact .ref (hcdMono_dt g args concName hdt hsome)
    · -- mono-miss arm: would produce `.ref g` for polymorphic g, but
      -- `hAppCovered` guarantees mono has an entry at `(g, args)` since
      -- `Typ.containsApp.here` witnesses the .app.
      rename_i hnone
      obtain ⟨concName, hsome⟩ := hAppCovered g args .here
      rw [hsome] at hnone
      cases hnone
  | @tuple ts _ ih =>
    intro hAppCovered t_cd htc
    simp only [typToConcrete, bind, Except.bind, pure, Except.pure] at htc
    split at htc
    · cases htc
    rename_i ts' hmap
    simp only [Except.ok.injEq] at htc
    cases htc
    refine .tuple ?_
    have hmap' : ts.mapM (fun t => typToConcrete mono t) = .ok ts' := by
      rw [Array.mapM_subtype (g := fun t => typToConcrete mono t) (fun _ _ => rfl)] at hmap
      rw [Array.unattach_attach] at hmap
      exact hmap
    intro t_cd_elem ht_cd_mem_list
    have ht_cd_mem : t_cd_elem ∈ ts' :=
      Array.mem_toList_iff.mp ht_cd_mem_list
    refine Array.mem_mapM_ok_forall
      (P := fun x => x ∈ ts)
      (Q := fun tc => Concrete.Typ.RefClosed cd tc)
      ?_ ts ts' (fun x hx => hx) hmap' t_cd_elem ht_cd_mem
    intro x hxMem fx hfx
    refine ih x hxMem ?_ hfx
    intro g0 args0 hcontain
    exact hAppCovered g0 args0 (.underTupleElt hxMem hcontain)
  | @array t n _ iht =>
    intro hAppCovered t_cd htc
    simp only [typToConcrete, bind, Except.bind, pure, Except.pure] at htc
    split at htc
    · cases htc
    rename_i t' hinner
    simp only [Except.ok.injEq] at htc
    cases htc
    refine .array (iht ?_ hinner)
    intro g0 args0 hcontain
    exact hAppCovered g0 args0 (.underArray hcontain)
  | @pointer t _ iht =>
    intro hAppCovered t_cd htc
    simp only [typToConcrete, bind, Except.bind, pure, Except.pure] at htc
    split at htc
    · cases htc
    rename_i t' hinner
    simp only [Except.ok.injEq] at htc
    cases htc
    refine .pointer (iht ?_ hinner)
    intro g0 args0 hcontain
    exact hAppCovered g0 args0 (.underPointer hcontain)
  | @function ins out _ _ _ _ =>
    intro _ t_cd htc
    simp only [typToConcrete, bind, Except.bind, pure, Except.pure] at htc
    split at htc
    · cases htc
    split at htc
    · cases htc
    rename_i out' hout' ins' hins'
    simp only [Except.ok.injEq] at htc
    cases htc
    exact .function

/-- Pure-structural helper: a typed type that `TypNoAppRefDtKey tds`-validates
syntactically forbids the `.app` constructor at every position. Hence
`Typ.containsApp g args t` is FALSE whenever `TypNoAppRefDtKey tds t` holds.

Used by `appsResolved_after_pipeline` (below) to discharge the mono-miss arm
of `typToConcrete_RefClosed_via_AppRefToDtOrNewDt` (helper #5) when the input
type `t` was produced by the concretize pipeline (post-`rewriteTyp ∅ drained.mono`)
on a tds-decl whose pre-image was `TypOkForRewrite drained.mono tds`-covered. -/
theorem containsApp_false_of_TypNoAppRefDtKey
    {tds : Typed.Decls} :
    ∀ {t : Typ}, TypNoAppRefDtKey tds t →
      ∀ g args, Typ.containsApp g args t → False := by
  intro t hNoApp g args hcontain
  induction hcontain with
  | here =>
    -- `TypNoAppRefDtKey tds (.app g args)` has no constructor — vacuous.
    cases hNoApp
  | @underAppArg g0 args0 t' _hmem _hsub _ih =>
    -- Same reason: outer `.app g0 args0` has no `TypNoAppRefDtKey` constructor.
    cases hNoApp
  | @underTupleElt ts t' hmem _hsub ih =>
    cases hNoApp with
    | tuple hsub =>
      exact ih (hsub t' (Array.mem_toList_iff.mpr hmem))
  | @underArray t' n _hsub ih =>
    cases hNoApp with
    | array hinner => exact ih hinner
  | @underPointer t' _hsub ih =>
    cases hNoApp with
    | pointer hinner => exact ih hinner
  | @underFunctionIn ins out t' hmem _hsub ih =>
    cases hNoApp with
    | function hi _ho => exact ih (hi t' hmem)
  | @underFunctionOut ins out _hsub ih =>
    cases hNoApp with
    | function _hi ho => exact ih ho

/-- Bridge lemma (shared discharge point): for any `Typ` `t` produced by the
concretize pipeline (post-`rewriteTyp drained.mono` on a `TypOkForRewrite`-
covered pre-image), no `.app g args` survives in `t`. Hence the
`Typ.containsApp` premise is vacuously satisfiable.

Strengthened 2026-04-30: takes a `TypNoAppRefDtKey tds t` hypothesis directly.
The structural part of "pipeline produces no `.app`" is closed here via
`containsApp_false_of_TypNoAppRefDtKey`. The pipeline-context part —
proving `TypNoAppRefDtKey tds t` for `t = (rewriteTyp ∅ drained.mono pre)` at
the call sites — is the residual obligation, now factored to each call site
as a focused per-site `BLOCKED-monoDecls-types-noAppRefDtKey-entry` sorry.

The closure path for that residual is:
  1. The full version `monoDecls_types_noAppRefDtKey` (RefClosed.lean:2372)
     already proves the claim under `FullyMonomorphic t`.
  2. The umbrella `Toplevel.concretize_produces_refClosed_entry` does NOT have
     `FullyMonomorphic t` — it only has `WellFormed t`.
  3. Need an entry-restricted analog `monoDecls_types_noAppRefDtKey_entry`
     that drops the `FullyMonomorphic` requirement. Path:
     - Generalize `concretizeSeed_covers_tds_apps` (DrainInvariants.lean:1183)
       to only cover monomorphic tds-decls (`f.params.isEmpty`/`dt.params.isEmpty`).
       The seed already filters by these flags, so the lemma should hold
       unconditionally (no FullyMono needed for monomorphic-decl coverage).
     - Generalize `DrainState.AppsReached` to a "monomorphic coverage" version.
     - Generalize `drainMono_coversTypesInTds` and `monoDecls_types_noAppRefDtKey`
       analogously.
     The change is mechanical: replace global `params.isEmpty` premises with
     "if .function f / .dataType dt then params.isEmpty" premises (always true
     by virtue of the source-side dispatch in concretizeBuild).

Estimated residual: ~120 LoC for the entry-restricted analog chain. -/
theorem appsResolved_after_pipeline
    {tds : Typed.Decls} {t : Typ}
    (hNoApp : TypNoAppRefDtKey tds t)
    (mono : Std.HashMap (Global × Array Typ) Global) :
    ∀ g args,
      Typ.containsApp g args t →
      ∃ concName, mono[(g, args)]? = some concName := by
  intro g args hcontain
  exact absurd (containsApp_false_of_TypNoAppRefDtKey hNoApp g args hcontain) id

/-! #### `appsResolved_after_pipeline_v2` — variant that takes the weaker
"no-app" hypothesis directly via mono coverage of the source-side `.app`s.

Closure path for the entry-restricted analog WITHOUT `FullyMonomorphic`:
- `concretizeSeed_covers_function_at_key` / `concretizeSeed_covers_dataType_at_key`
  / `concretizeSeed_covers_constructor_at_key` (DrainInvariants.lean) give per-decl
  coverage of source-side `.app`s by `concretizeSeed tds`, conditioned on
  `params.isEmpty` of the decl (a fact derivable at the umbrella's `name`).
- `concretize_drain_init_pending_in_seen` lifts `seed ⊆ drained.seen`.
- `SeenSubsetMono` (preserved through drain) lifts `drained.seen` ⊆
  `mono.dom` (`mono[(g,args)]? = some _`).
- `rewriteTyp_no_app_of_AllApps_covered` (below) shows the `.app`-replacement
  semantics: when mono covers all `.app`s in `src_t`, `rewriteTyp ∅ mono src_t`
  has no `.app`. The `containsApp` premise is then vacuously discharged.
-/

/-- Structural fact: `rewriteTyp` of a type whose every `.app g args` has a
mono entry produces a type with no `.app` constructor anywhere. -/
theorem rewriteTyp_no_app_of_AllApps_covered
    {mono : MonoMap} :
    ∀ {t : Typ}, Typ.AllAppsP (fun g args => mono[(g, args)]?.isSome) t →
      ∀ g args, ¬ Typ.containsApp g args (rewriteTyp (fun _ => none) mono t)
  | .unit, _, _, _, h => by
    unfold rewriteTyp at h; cases h
  | .field, _, _, _, h => by
    unfold rewriteTyp at h; cases h
  | .mvar n, _, _, _, h => by
    unfold rewriteTyp at h; cases h
  | .ref g0, _, _, _, h => by
    unfold rewriteTyp at h
    simp only [Option.getD_none] at h
    cases h
  | .pointer inner, hCov, g, args, h => by
    unfold rewriteTyp at h
    cases hCov with
    | pointer hi =>
      cases h with
      | underPointer h' =>
        exact rewriteTyp_no_app_of_AllApps_covered hi g args h'
  | .array t n, hCov, g, args, h => by
    unfold rewriteTyp at h
    cases hCov with
    | array hi =>
      cases h with
      | underArray h' =>
        exact rewriteTyp_no_app_of_AllApps_covered hi g args h'
  | .tuple ts, hCov, g, args, h => by
    unfold rewriteTyp at h
    cases hCov with
    | tuple hi =>
      cases h with
      | @underTupleElt _ t' hmem h' =>
        -- t' ∈ (ts.attach.map (fun ⟨t, _⟩ => rewriteTyp ∅ mono t))
        obtain ⟨t0, ht0_mem, ht0_eq⟩ := mem_of_attach_map ts _ hmem
        have ht0Cov : Typ.AllAppsP (fun g args => mono[(g, args)]?.isSome) t0 :=
          hi t0 (Array.mem_toList_iff.mpr ht0_mem)
        rw [← ht0_eq] at h'
        exact rewriteTyp_no_app_of_AllApps_covered ht0Cov g args h'
  | .function ins out, hCov, g, args, h => by
    unfold rewriteTyp at h
    cases hCov with
    | function hin hout =>
      cases h with
      | @underFunctionIn _ _ t' hmem h' =>
        obtain ⟨t0, ht0_mem, ht0_eq⟩ := list_mem_of_attach_map ins _ hmem
        have ht0Cov : Typ.AllAppsP (fun g args => mono[(g, args)]?.isSome) t0 :=
          hin t0 ht0_mem
        rw [← ht0_eq] at h'
        exact rewriteTyp_no_app_of_AllApps_covered ht0Cov g args h'
      | underFunctionOut h' =>
        exact rewriteTyp_no_app_of_AllApps_covered hout g args h'
  | .app g0 args0, hCov, g, args, h => by
    unfold rewriteTyp at h
    cases hCov with
    | app hsub hin =>
      -- mono[(g0, args0)]? has form some _ since `hin : mono[(g0, args0)]?.isSome`.
      cases hsome : mono[(g0, args0)]? with
      | none =>
        rw [hsome] at hin; cases hin
      | some concName =>
        rw [hsome] at h
        -- After rewriteTyp, .app becomes .ref concName, which has no .app.
        cases h
  termination_by t _ _ _ _ => sizeOf t
  decreasing_by
    all_goals first
      | decreasing_tactic
      | (have := Array.sizeOf_lt_of_mem ‹_ ∈ _›; grind)
      | (have := List.sizeOf_lt_of_mem ‹_ ∈ _›; grind)

/-- Variant of `appsResolved_after_pipeline` that takes the post-rewriteTyp
type's .app-coverage via the SOURCE-side mono coverage. -/
theorem appsResolved_after_pipeline_v2
    {mono : MonoMap} {src_t : Typ}
    (hCov : Typ.AllAppsP (fun g args => mono[(g, args)]?.isSome) src_t) :
    ∀ g args,
      Typ.containsApp g args (rewriteTyp (fun _ => none) mono src_t) →
      ∃ concName, (∅ : MonoMap)[(g, args)]? = some concName := by
  intro g args hcontain
  exact absurd (rewriteTyp_no_app_of_AllApps_covered hCov g args hcontain) id

/-- Lift per-decl seed coverage to drained.mono coverage via `init_pending_in_seen`
and `SeenSubsetMono`. -/
theorem mono_covers_of_seed_covered
    {tds : Typed.Decls} {drained : DrainState}
    (hSSM : drained.SeenSubsetMono)
    (hdrain : concretizeDrain tds (concretizeDrainFuel tds)
        { pending := concretizeSeed tds, seen := {}, mono := {},
          newFunctions := #[], newDataTypes := #[] } = .ok drained)
    {t : Typ}
    (hSeed : Typ.AllAppsP (fun g args => (g, args) ∈ concretizeSeed tds) t) :
    Typ.AllAppsP (fun g args => drained.mono[(g, args)]?.isSome) t := by
  apply hSeed.weaken
  intro g args hin
  -- (g, args) ∈ seed → ∈ drained.seen → drained.mono[(g,args)]? = some _.
  have hin_seen : (g, args) ∈ drained.seen :=
    concretize_drain_init_pending_in_seen _ _ hdrain (g, args) hin
  rw [hSSM g args hin_seen]
  rfl

/-- Helper to discharge `hAppCovered` for `typToConcrete_RefClosed_via_AppRefToDtOrNewDt`
when `t = rewriteTyp ∅ drained.mono src_t` and `src_t` is a type from a
`params=[]` source decl: the `.app`s of `src_t` are mono-covered, so the
rewriteTyp result has no `.app`, making the `containsApp` premise vacuous.

This is the entry-restricted analog of `appsResolved_after_pipeline` that
does NOT require `FullyMonomorphic`. -/
theorem appsResolved_via_seed_coverage
    {tds : Typed.Decls} {drained : DrainState} {src_t : Typ}
    (hSSM : drained.SeenSubsetMono)
    (hdrain : concretizeDrain tds (concretizeDrainFuel tds)
        { pending := concretizeSeed tds, seen := {}, mono := {},
          newFunctions := #[], newDataTypes := #[] } = .ok drained)
    (hSeed : Typ.AllAppsP (fun g args => (g, args) ∈ concretizeSeed tds) src_t)
    (mono : MonoMap) :
    ∀ g args,
      Typ.containsApp g args (rewriteTyp (fun _ => none) drained.mono src_t) →
      ∃ concName, mono[(g, args)]? = some concName := by
  intro g args hcontain
  have hMonoCov : Typ.AllAppsP (fun g args => drained.mono[(g, args)]?.isSome) src_t :=
    mono_covers_of_seed_covered hSSM hdrain hSeed
  exact absurd (rewriteTyp_no_app_of_AllApps_covered hMonoCov g args hcontain) id

/-- Variant taking `AllAppsP (∈ drained.seen) src_t` directly. Used in the
`AppsReachedCond` post-drain dispatch: after drain (`pending = ∅`),
`AppsReachedCond` collapses to `AllAppsP (∈ seen)`-coverage of source-decl
types. SeenSubsetMono lifts to mono-coverage. -/
theorem appsResolved_via_seen_coverage_rewrite
    {drained : DrainState} {src_t : Typ}
    (hSSM : drained.SeenSubsetMono)
    (hSeen : Typ.AllAppsP (fun g args => (g, args) ∈ drained.seen) src_t)
    (mono : MonoMap) :
    ∀ g args,
      Typ.containsApp g args (rewriteTyp (fun _ => none) drained.mono src_t) →
      ∃ concName, mono[(g, args)]? = some concName := by
  intro g args hcontain
  have hMonoCov : Typ.AllAppsP (fun g args => drained.mono[(g, args)]?.isSome) src_t := by
    apply hSeen.weaken
    intro g0 args0 hin
    rw [hSSM g0 args0 hin]; rfl
  exact absurd (rewriteTyp_no_app_of_AllApps_covered hMonoCov g args hcontain) id

/-- Step-wise invariant: if the accumulator satisfies `AllRefsTargetTds` AND
the next input `d_mono`'s types all satisfy `TypNoAppRefDtKey tds`, then the
post-step4Lower accumulator satisfies `AllRefsTargetTds`. -/
theorem step4Lower_preserves_AllRefsTargetTds
    {tds : Typed.Decls} {acc : Concrete.Decls} {name : Global}
    {d_mono : Typed.Declaration} {acc' : Concrete.Decls}
    (hacc : AllRefsTargetTds acc tds)
    (hd : declTypesNoAppRefDtKey tds d_mono)
    (hstep : step4Lower acc (name, d_mono) = .ok acc') :
    AllRefsTargetTds acc' tds := by
  intro key d_cd hget_cd
  unfold step4Lower at hstep
  cases d_mono with
  | function f =>
    simp only [bind, Except.bind, pure, Except.pure] at hstep
    split at hstep
    · cases hstep
    rename_i ins' hins'
    split at hstep
    · cases hstep
    rename_i out' hout'
    split at hstep
    · cases hstep
    rename_i body' hbody'
    simp only [Except.ok.injEq] at hstep
    subst hstep
    by_cases hkey : (name == key) = true
    · have hkey_eq : name = key := LawfulBEq.eq_of_beq hkey
      subst hkey_eq
      rw [IndexMap.getByKey_insert_self] at hget_cd
      cases hget_cd
      simp only [declTypesNoAppRefDtKey] at hd
      obtain ⟨hdi, hdo⟩ := hd
      refine ⟨?_, ?_⟩
      · -- Inputs: propagate via `List.mem_mapM_ok_forall`.
        -- `hins' : f.inputs.mapM (fun (l,t) => do let t' ← typToConcrete {} t; pure (l, t')) = .ok ins'`
        -- P := fun (lt : Local × Typ) => TypNoAppRefDtKey tds lt.snd
        -- Q := fun (lt' : Local × Concrete.Typ) => RefTargetsInTds tds lt'.snd
        refine List.mem_mapM_ok_forall
          (P := fun lt => TypNoAppRefDtKey tds lt.snd)
          (Q := fun lt' => RefTargetsInTds tds lt'.snd) ?_ f.inputs ins' hdi hins'
        intro ⟨l, t⟩ hP fx hfx
        simp only [bind, Except.bind, pure, Except.pure] at hfx
        split at hfx
        · cases hfx
        rename_i t' ht'
        simp only [Except.ok.injEq] at hfx
        subst hfx
        exact typToConcrete_preserves_RefTargetsInTds hP ht'
      · -- Output.
        exact typToConcrete_preserves_RefTargetsInTds hdo hout'
    · have hne : (name == key) = false := Bool.not_eq_true _ |>.mp hkey
      rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget_cd
      exact hacc key d_cd hget_cd
  | dataType dt =>
    simp only [bind, Except.bind, pure, Except.pure] at hstep
    split at hstep
    · cases hstep
    rename_i ctors' hctors'
    simp only [Except.ok.injEq] at hstep
    subst hstep
    by_cases hkey : (name == key) = true
    · have hkey_eq : name = key := LawfulBEq.eq_of_beq hkey
      subst hkey_eq
      rw [IndexMap.getByKey_insert_self] at hget_cd
      cases hget_cd
      simp only [declTypesNoAppRefDtKey] at hd
      intro c hc t ht
      -- Thread via mem_mapM_ok_forall twice: outer over `dt.constructors → ctors'`,
      -- inner over `src.argTypes → c.argTypes` (= argTypes').
      -- Outer P: all ctor argTypes satisfy TypNoAppRefDtKey. Q: all ctor argTypes
      -- (concrete) satisfy RefTargetsInTds.
      refine List.mem_mapM_ok_forall
        (P := fun c : Constructor =>
          ∀ t ∈ c.argTypes, TypNoAppRefDtKey tds t)
        (Q := fun cc : Concrete.Constructor =>
          ∀ t ∈ cc.argTypes, RefTargetsInTds tds t) ?_ dt.constructors ctors' hd hctors' c hc t ht
      intro cSrc hPc fcc hfcc
      -- fcc = ⟨cSrc.nameHead, argTypes'⟩ where cSrc.argTypes.mapM (typToConcrete {}) = .ok argTypes'.
      simp only [bind, Except.bind, pure, Except.pure] at hfcc
      split at hfcc
      · cases hfcc
      rename_i argTypes' hargTypes'
      simp only [Except.ok.injEq] at hfcc
      subst hfcc
      -- Apply inner mem_mapM_ok_forall: P := TypNoAppRefDtKey, Q := RefTargetsInTds.
      exact List.mem_mapM_ok_forall
        (P := fun t => TypNoAppRefDtKey tds t)
        (Q := fun t' => RefTargetsInTds tds t')
        (fun x hP' fx hfx => typToConcrete_preserves_RefTargetsInTds hP' hfx)
        cSrc.argTypes argTypes' hPc hargTypes'
    · have hne : (name == key) = false := Bool.not_eq_true _ |>.mp hkey
      rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget_cd
      exact hacc key d_cd hget_cd
  | constructor dt c =>
    simp only [bind, Except.bind, pure, Except.pure] at hstep
    split at hstep
    · cases hstep
    rename_i ctors' hctors'
    split at hstep
    · cases hstep
    rename_i argTypes' hargTypes'
    simp only [Except.ok.injEq] at hstep
    subst hstep
    by_cases hkey : (name == key) = true
    · have hkey_eq : name = key := LawfulBEq.eq_of_beq hkey
      subst hkey_eq
      rw [IndexMap.getByKey_insert_self] at hget_cd
      cases hget_cd
      simp only [declTypesNoAppRefDtKey] at hd
      intro t ht
      -- ht : t ∈ argTypes' (= concC.argTypes).
      exact List.mem_mapM_ok_forall
        (P := fun t => TypNoAppRefDtKey tds t)
        (Q := fun t' => RefTargetsInTds tds t')
        (fun x hP' fx hfx => typToConcrete_preserves_RefTargetsInTds hP' hfx)
        c.argTypes argTypes' hd hargTypes' t ht
    · have hne : (name == key) = false := Bool.not_eq_true _ |>.mp hkey
      rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget_cd
      exact hacc key d_cd hget_cd

/-- Fold preservation: `foldlM step4Lower` preserves `AllRefsTargetTds`
when every input pair's `d_mono` satisfies `declTypesNoAppRefDtKey`. -/
theorem step4Lower_foldlM_preserves_AllRefsTargetTds
    {tds : Typed.Decls} :
    ∀ (pairs : List (Global × Typed.Declaration))
      (init result : Concrete.Decls)
      (_hinit : AllRefsTargetTds init tds)
      (_hpairs : ∀ p ∈ pairs, declTypesNoAppRefDtKey tds p.snd)
      (_hfold : _root_.List.foldlM step4Lower init pairs = .ok result),
      AllRefsTargetTds result tds
  | [], init, result, hinit, _, hfold => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at hfold
    subst hfold; exact hinit
  | hd :: tl, init, result, hinit, hpairs, hfold => by
    simp only [List.foldlM_cons, bind, Except.bind] at hfold
    cases hstep : step4Lower init hd with
    | error e => rw [hstep] at hfold; cases hfold
    | ok acc' =>
      rw [hstep] at hfold
      have hhd : declTypesNoAppRefDtKey tds hd.snd :=
        hpairs hd List.mem_cons_self
      have hacc' : AllRefsTargetTds acc' tds := by
        obtain ⟨n, d⟩ := hd
        exact step4Lower_preserves_AllRefsTargetTds hinit hhd hstep
      exact step4Lower_foldlM_preserves_AllRefsTargetTds tl acc' result hacc'
        (fun p hp => hpairs p (List.mem_cons_of_mem _ hp)) hfold

/-! #### Sub-blocker infrastructure: `TypOkForRewrite` + `rewriteTyp` preservation.

The sub-blocker `monoDecls_types_noAppRefDtKey` is factored as:

1. `TypOkForRewrite mono tds t` — joint structural predicate on pre-rewrite
   typed types: every `.ref g'` is a tds dt-key, every `.app g args` has
   a mono entry `(g, args) ↦ g'` with `g'` a tds dt-key (recursively on
   args, pointer, tuple, array).
2. `rewriteTyp_preserves_TypNoAppRefDtKey` — if `TypOkForRewrite mono tds t`,
   then `rewriteTyp emptySubst mono t` satisfies `TypNoAppRefDtKey tds`.
   The `.function` arm is vacuous (no nested IH, no structural obligation);
   the `TypOkForRewrite.function` constructor matches
   `TypNoAppRefDtKey.function` without extra obligations, but we must
   still produce witnesses for `TypNoAppRefDtKey.function`'s ins/out
   components. Since these cannot be produced without additional hypotheses,
   we short-circuit: the `rewriteTyp` on `.function` produces `.function`
   too, and we construct the `TypNoAppRefDtKey.function` with universally
   vacuous witnesses (its hypothesis is `∀ t ∈ ins, TypNoAppRefDtKey tds t`
   on the rewritten ins, which is not vacuous — so the `.function` arm is
   actually non-trivial). We therefore require the stronger joint predicate
   that recurses on `.function` components.
3. Per-phase helpers for `concretizeBuild`'s 3-fold structure.
4. `drainMono_coversTypesInTds` (single residual sorry): for every type in
   tds / drained.newFunctions / drained.newDataTypes, `TypOkForRewrite
   drained.mono tds` holds. BLOCKED on new `DrainState.AppMonoCovers`
   invariant chain (~400 LoC). -/

/-- Joint structural predicate: every `.ref g'` in `t` is a tds dt-key, and
every `.app g args` occurrence has a mono-map entry `(g, args) ↦ g'` with
`g'` a tds dt-key (plus recursive args). Also recurses structurally through
`.pointer` / `.tuple` / `.array` / `.function`. -/
inductive TypOkForRewrite (mono : MonoMap) (tds : Typed.Decls) : Typ → Prop
  | unit    : TypOkForRewrite mono tds .unit
  | field   : TypOkForRewrite mono tds .field
  | mvar n  : TypOkForRewrite mono tds (.mvar n)
  | pointer {inner} (h : TypOkForRewrite mono tds inner) :
      TypOkForRewrite mono tds (.pointer inner)
  | tuple {ts} (h : ∀ t ∈ ts.toList, TypOkForRewrite mono tds t) :
      TypOkForRewrite mono tds (.tuple ts)
  | array {t n} (h : TypOkForRewrite mono tds t) :
      TypOkForRewrite mono tds (.array t n)
  | function {ins out}
      (hi : ∀ t ∈ ins, TypOkForRewrite mono tds t)
      (ho : TypOkForRewrite mono tds out) :
      TypOkForRewrite mono tds (.function ins out)
  | ref {g} (hdt : ∃ dt, tds.getByKey g = some (.dataType dt)) :
      TypOkForRewrite mono tds (.ref g)
  | app {g args}
      (h : ∀ t ∈ args.toList, TypOkForRewrite mono tds t)
      (hmono : ∃ g' dt, mono[(g, args)]? = some g' ∧
        tds.getByKey g' = some (.dataType dt)) :
      TypOkForRewrite mono tds (.app g args)

/-- Structural preservation. -/
theorem rewriteTyp_preserves_TypNoAppRefDtKey
    {mono : MonoMap} {tds : Typed.Decls} :
    ∀ (typ : Typ), TypOkForRewrite mono tds typ →
      TypNoAppRefDtKey tds (rewriteTyp (fun _ => none) mono typ)
  | .unit, _ => by unfold rewriteTyp; exact .unit
  | .field, _ => by unfold rewriteTyp; exact .field
  | .mvar n, _ => by unfold rewriteTyp; exact .mvar n
  | .pointer inner, h => by
    unfold rewriteTyp
    cases h with
    | pointer hinner =>
      exact .pointer (rewriteTyp_preserves_TypNoAppRefDtKey inner hinner)
  | .array ta n, h => by
    unfold rewriteTyp
    cases h with
    | array hinner =>
      exact .array (rewriteTyp_preserves_TypNoAppRefDtKey ta hinner)
  | .tuple ts, h => by
    unfold rewriteTyp
    cases h with
    | tuple hsub =>
      refine TypNoAppRefDtKey.tuple ?_
      intro t ht
      obtain ⟨u, hu_mem, hu_eq⟩ := mem_of_attach_map ts _ (Array.mem_toList_iff.mp ht)
      have huOk : TypOkForRewrite mono tds u :=
        hsub u (Array.mem_toList_iff.mpr hu_mem)
      have := rewriteTyp_preserves_TypNoAppRefDtKey u huOk
      rw [← hu_eq]; exact this
  | .function ins out, h => by
    unfold rewriteTyp
    cases h with
    | function hi ho =>
      refine TypNoAppRefDtKey.function ?_ ?_
      · intro t ht
        obtain ⟨u, hu_mem, hu_eq⟩ := list_mem_of_attach_map ins _ ht
        have huOk : TypOkForRewrite mono tds u := hi u hu_mem
        have := rewriteTyp_preserves_TypNoAppRefDtKey u huOk
        rw [← hu_eq]; exact this
      · exact rewriteTyp_preserves_TypNoAppRefDtKey out ho
  | .ref g, h => by
    unfold rewriteTyp
    cases h with
    | ref hdt =>
      -- `fun _ => none` applied to g gives `none`, so `.ref g` stays.
      show TypNoAppRefDtKey tds (Option.getD none (Typ.ref g))
      exact .ref hdt
  | .app g args, h => by
    unfold rewriteTyp
    cases h with
    | app _hsub hmono =>
      obtain ⟨g', dt', hmono_eq, hget⟩ := hmono
      rw [hmono_eq]
      exact .ref ⟨dt', hget⟩
  termination_by typ => sizeOf typ
  decreasing_by
    all_goals first
      | decreasing_tactic
      | (have := Array.sizeOf_lt_of_mem ‹_ ∈ _›; grind)

/-- Translation: `Typ.AllAppsP (∈ seen) t` + `TypRefsAreDtKeys tds t` plus
strong-SeenSubsetMono and tds-dt-params-empty give `TypOkForRewrite mono tds t`.
Under FullyMono, `dt.params = []` ⟹ `args.size = 0` ⟹ `args = #[]` ⟹
`concretizeName g #[] = g` ⟹ mono target = source `g` (which is a tds dt-key). -/
theorem typOkForRewrite_of_apps_in_seen
    (mono : MonoMap) (tds : Typed.Decls) (seen : Std.HashSet (Global × Array Typ))
    (hSeenSubsetMono : ∀ g args, (g, args) ∈ seen →
      mono[(g, args)]? = some (concretizeName g args))
    (hParamsEmpty : ∀ g dt, tds.getByKey g = some (.dataType dt) → dt.params = []) :
    ∀ (t : Typ), TypRefsAreDtKeys tds t →
      Typ.AllAppsP (fun g args => (g, args) ∈ seen) t →
      TypOkForRewrite mono tds t
  | .unit, _, _ => .unit
  | .field, _, _ => .field
  | .mvar n, _, _ => .mvar n
  | .pointer inner, hr, ha => by
    cases hr with
    | pointer hr_inner =>
      cases ha with
      | pointer ha_inner =>
        exact .pointer (typOkForRewrite_of_apps_in_seen mono tds seen
          hSeenSubsetMono hParamsEmpty inner hr_inner ha_inner)
  | .array t n, hr, ha => by
    cases hr with
    | array hr_inner =>
      cases ha with
      | array ha_inner =>
        exact .array (typOkForRewrite_of_apps_in_seen mono tds seen
          hSeenSubsetMono hParamsEmpty t hr_inner ha_inner)
  | .tuple ts, hr, ha => by
    cases hr with
    | tuple hr_subs =>
      cases ha with
      | tuple ha_subs =>
        refine .tuple ?_
        intro t' ht'
        have hmem : t' ∈ ts := Array.mem_toList_iff.mp ht'
        exact typOkForRewrite_of_apps_in_seen mono tds seen
          hSeenSubsetMono hParamsEmpty t' (hr_subs t' ht') (ha_subs t' ht')
  | .function ins out, hr, ha => by
    cases hr with
    | function hr_in hr_out =>
      cases ha with
      | function ha_in ha_out =>
        refine .function ?_ ?_
        · intro t' ht'
          exact typOkForRewrite_of_apps_in_seen mono tds seen
            hSeenSubsetMono hParamsEmpty t' (hr_in t' ht') (ha_in t' ht')
        · exact typOkForRewrite_of_apps_in_seen mono tds seen
            hSeenSubsetMono hParamsEmpty out hr_out ha_out
  | .ref g, hr, _ => by
    cases hr with
    | ref hdt => exact .ref hdt
  | .app g args, hr, ha => by
    cases hr with
    | app hdt_g hr_args =>
      cases ha with
      | app ha_args ha_in =>
        refine .app ?_ ?_
        · intro t' ht'
          have hmem : t' ∈ args := Array.mem_toList_iff.mp ht'
          exact typOkForRewrite_of_apps_in_seen mono tds seen
            hSeenSubsetMono hParamsEmpty t' (hr_args t' ht') (ha_args t' ht')
        · obtain ⟨dt, hdt_get, hsize⟩ := hdt_g
          have hparams : dt.params = [] := hParamsEmpty g dt hdt_get
          have hsize0 : args.size = 0 := by rw [hsize, hparams]; rfl
          have hargs_empty : args = #[] := Array.size_eq_zero_iff.mp hsize0
          have hmono := hSeenSubsetMono g args ha_in
          subst hargs_empty
          rw [concretizeName_empty_args] at hmono
          exact ⟨g, dt, hmono, hdt_get⟩
  termination_by t _ _ => sizeOf t
  decreasing_by
    all_goals first
      | decreasing_tactic
      | (have := Array.sizeOf_lt_of_mem ‹_ ∈ _›; grind)
      | (have := List.sizeOf_lt_of_mem ‹_ ∈ _›; grind)

/-! ### `NewDeclTypesRefsOk` — drain invariant: every type in
`newFunctions` / `newDataTypes` satisfies `TypRefsAreDtKeys tds`.

Under FullyMono (`f.params = []` and `dt.params = []` for all `tds`-decls),
each pushed `newFn`/`newDt` has its types built via
`Typ.instantiate (mkParamSubst [] args) = Typ.instantiate (fun _ => none)`,
which is identity on `Typ` (`Typ.instantiate_empty_id`). So the new types
LITERALLY equal the source decl's types, and `TypRefsAreDtKeys` lifts
directly via `AllRefsAreDtKeys` (L1). -/

def DrainState.NewDeclTypesRefsOk (tds : Typed.Decls) (st : DrainState) : Prop :=
  (∀ dt ∈ st.newDataTypes, ∀ c ∈ dt.constructors, ∀ ty ∈ c.argTypes,
      TypRefsAreDtKeys tds ty) ∧
  (∀ f ∈ st.newFunctions,
      (∀ lt ∈ f.inputs, TypRefsAreDtKeys tds lt.snd) ∧
      TypRefsAreDtKeys tds f.output)

theorem DrainState.NewDeclTypesRefsOk.init {tds : Typed.Decls}
    (pending : Std.HashSet (Global × Array Typ)) :
    DrainState.NewDeclTypesRefsOk tds
      { pending, seen := {}, mono := {}, newFunctions := #[], newDataTypes := #[] } := by
  refine ⟨?_, ?_⟩
  · intro dt hdt; simp only [Array.not_mem_empty] at hdt
  · intro f hf; simp only [Array.not_mem_empty] at hf

theorem concretizeDrainEntry_preserves_NewDeclTypesRefsOk
    {tds : Typed.Decls}
    (hL1 : AllRefsAreDtKeys tds)
    (hfn_params : ∀ key f, tds.getByKey key = some (.function f) → f.params = [])
    (hdt_params : ∀ key dt, tds.getByKey key = some (.dataType dt) → dt.params = [])
    {state state' : DrainState}
    (hinv : DrainState.NewDeclTypesRefsOk tds state) (entry : Global × Array Typ)
    (hstep : concretizeDrainEntry tds state entry = .ok state') :
    DrainState.NewDeclTypesRefsOk tds state' := by
  unfold concretizeDrainEntry at hstep
  simp only [bind, Except.bind, pure, Except.pure] at hstep
  by_cases hseen : state.seen.contains (entry.1, entry.2)
  · simp [hseen] at hstep
    rw [← hstep]; exact hinv
  · simp [hseen] at hstep
    split at hstep
    · rename_i f hf_get
      split at hstep
      · simp only [Except.ok.injEq] at hstep
        rw [← hstep]
        refine ⟨hinv.1, ?_⟩
        intro f' hf'mem
        rcases Array.mem_push.mp hf'mem with hin | heq
        · exact hinv.2 f' hin
        · subst heq
          simp only
          have hpe : f.params = [] := hfn_params entry.1 f hf_get
          have hsubst : mkParamSubst f.params entry.2 = (fun _ => none) := by
            rw [hpe, mkParamSubst_nil]
          have hL1_f := hL1 entry.1 (.function f) hf_get
          simp only at hL1_f
          obtain ⟨hL1_in, hL1_out⟩ := hL1_f
          refine ⟨?_, ?_⟩
          · intro lt hlt
            simp only [List.mem_map] at hlt
            obtain ⟨lt_orig, hlt_orig, heq⟩ := hlt
            rw [← heq]
            simp only [hsubst, Typ.instantiate_empty_id]
            exact hL1_in lt_orig hlt_orig
          · simp only [hsubst, Typ.instantiate_empty_id]
            exact hL1_out
      · exact absurd hstep (by intro h; cases h)
    · rename_i dt hdt_get
      split at hstep
      · simp only [Except.ok.injEq] at hstep
        rw [← hstep]
        refine ⟨?_, hinv.2⟩
        intro dt' hdt'mem
        rcases Array.mem_push.mp hdt'mem with hin | heq
        · exact hinv.1 dt' hin
        · subst heq
          have hpe : dt.params = [] := hdt_params entry.1 dt hdt_get
          have hsubst : mkParamSubst dt.params entry.2 = (fun _ => none) := by
            rw [hpe, mkParamSubst_nil]
          have hL1_dt := hL1 entry.1 (.dataType dt) hdt_get
          simp only at hL1_dt
          intro c hc ty hty
          rw [List.mem_map] at hc
          obtain ⟨c_orig, hc_orig, hc_eq⟩ := hc
          subst hc_eq
          simp only at hty
          rw [hsubst, List.mem_map] at hty
          obtain ⟨ty_orig, hty_orig, hty_eq⟩ := hty
          rw [← hty_eq, Typ.instantiate_empty_id]
          exact hL1_dt c_orig hc_orig ty_orig hty_orig
      · exact absurd hstep (by intro h; cases h)
    · cases hstep

theorem concretizeDrainEntry_list_foldlM_preserves_NewDeclTypesRefsOk
    {tds : Typed.Decls}
    (hL1 : AllRefsAreDtKeys tds)
    (hfn_params : ∀ key f, tds.getByKey key = some (.function f) → f.params = [])
    (hdt_params : ∀ key dt, tds.getByKey key = some (.dataType dt) → dt.params = [])
    (L : List (Global × Array Typ))
    (state0 state' : DrainState)
    (hinv0 : DrainState.NewDeclTypesRefsOk tds state0)
    (hstep : L.foldlM (concretizeDrainEntry tds) state0 = .ok state') :
    DrainState.NewDeclTypesRefsOk tds state' := by
  induction L generalizing state0 with
  | nil =>
    simp only [List.foldlM, pure, Except.pure, Except.ok.injEq] at hstep
    rw [← hstep]; exact hinv0
  | cons hd tl ih =>
    simp only [List.foldlM, bind, Except.bind] at hstep
    split at hstep
    · cases hstep
    · rename_i s'' hs''
      have hinv1 : DrainState.NewDeclTypesRefsOk tds s'' :=
        concretizeDrainEntry_preserves_NewDeclTypesRefsOk hL1 hfn_params hdt_params
          hinv0 hd hs''
      exact ih s'' hinv1 hstep

theorem concretizeDrainIter_preserves_NewDeclTypesRefsOk
    {tds : Typed.Decls}
    (hL1 : AllRefsAreDtKeys tds)
    (hfn_params : ∀ key f, tds.getByKey key = some (.function f) → f.params = [])
    (hdt_params : ∀ key dt, tds.getByKey key = some (.dataType dt) → dt.params = [])
    {state state' : DrainState}
    (hinv : DrainState.NewDeclTypesRefsOk tds state)
    (hstep : concretizeDrainIter tds state = .ok state') :
    DrainState.NewDeclTypesRefsOk tds state' := by
  unfold concretizeDrainIter at hstep
  rw [← Array.foldlM_toList] at hstep
  let state0 : DrainState := { state with pending := ∅ }
  have hinv0 : DrainState.NewDeclTypesRefsOk tds state0 := hinv
  exact concretizeDrainEntry_list_foldlM_preserves_NewDeclTypesRefsOk hL1
    hfn_params hdt_params state.pending.toArray.toList state0 state' hinv0 hstep

theorem concretize_drain_preserves_NewDeclTypesRefsOk
    {tds : Typed.Decls}
    (hL1 : AllRefsAreDtKeys tds)
    (hfn_params : ∀ key f, tds.getByKey key = some (.function f) → f.params = [])
    (hdt_params : ∀ key dt, tds.getByKey key = some (.dataType dt) → dt.params = [])
    (fuel : Nat) (init : DrainState)
    (hinv : DrainState.NewDeclTypesRefsOk tds init)
    {drained : DrainState}
    (hdrain : concretizeDrain tds fuel init = .ok drained) :
    DrainState.NewDeclTypesRefsOk tds drained := by
  induction fuel generalizing init with
  | zero =>
    unfold concretizeDrain at hdrain
    by_cases hpen : init.pending.isEmpty
    · simp only [hpen, if_true, pure, Except.pure, Except.ok.injEq] at hdrain
      rw [← hdrain]; exact hinv
    · simp [hpen] at hdrain
  | succ n ih =>
    unfold concretizeDrain at hdrain
    by_cases hpen : init.pending.isEmpty
    · simp only [hpen, if_true, pure, Except.pure, Except.ok.injEq] at hdrain
      rw [← hdrain]; exact hinv
    · simp only [hpen, if_false, Bool.false_eq_true] at hdrain
      simp only [bind, Except.bind] at hdrain
      split at hdrain
      · cases hdrain
      · rename_i state' hstate'
        have hinv' : DrainState.NewDeclTypesRefsOk tds state' :=
          concretizeDrainIter_preserves_NewDeclTypesRefsOk hL1 hfn_params hdt_params
            hinv hstate'
        exact ih state' hinv' hdrain

/-- **Single residual sorry (Layer A+B)**: every type appearing in any tds
declaration, or any drained newFunction/newDataType, satisfies
`TypOkForRewrite drained.mono tds`. BLOCKED on new DrainState invariant
chain (`AppMonoCovers`, ~400 LoC parallel to `NewNameShape`). -/
theorem drainMono_coversTypesInTds
    {t : Source.Toplevel} {tds : Typed.Decls}
    {drained : DrainState}
    (hmono : FullyMonomorphic t)
    (hts : t.checkAndSimplify = .ok tds)
    (hL1 : AllRefsAreDtKeys tds)
    (hdrain : concretizeDrain tds (concretizeDrainFuel tds)
        { pending := concretizeSeed tds, seen := {}, mono := {},
          newFunctions := #[], newDataTypes := #[] } = .ok drained) :
    (∀ key d_src, tds.getByKey key = some d_src →
      match d_src with
      | .function f =>
          (∀ lt ∈ f.inputs, TypOkForRewrite drained.mono tds lt.snd) ∧
          TypOkForRewrite drained.mono tds f.output
      | .dataType dt =>
          ∀ c ∈ dt.constructors, ∀ ty ∈ c.argTypes,
            TypOkForRewrite drained.mono tds ty
      | .constructor _ c =>
          ∀ ty ∈ c.argTypes, TypOkForRewrite drained.mono tds ty) ∧
    (∀ dt ∈ drained.newDataTypes, ∀ c ∈ dt.constructors, ∀ ty ∈ c.argTypes,
        TypOkForRewrite drained.mono tds ty) ∧
    (∀ f ∈ drained.newFunctions,
      (∀ lt ∈ f.inputs, TypOkForRewrite drained.mono tds lt.snd) ∧
      TypOkForRewrite drained.mono tds f.output) := by
  -- Source decls.
  have ⟨decls, hdecls, _⟩ : ∃ decls, t.mkDecls = .ok decls ∧ True := by
    unfold Source.Toplevel.checkAndSimplify at hts
    simp only [bind, Except.bind] at hts
    split at hts
    · cases hts
    rename_i srcDecls hmk
    exact ⟨srcDecls, hmk, trivial⟩
  -- Params-empty + ctor-companion under FullyMono.
  have hfn_params_empty_eq : ∀ key f, tds.getByKey key = some (.function f) →
      f.params = [] := typedDecls_params_empty_of_fullyMonomorphic hmono hdecls hts
  have hdt_params_empty_eq : ∀ key dt, tds.getByKey key = some (.dataType dt) →
      dt.params = [] := typedDecls_dt_params_empty_of_fullyMonomorphic hmono hdecls hts
  have hfn_params_empty : ∀ key f, tds.getByKey key = some (.function f) →
      f.params.isEmpty := fun key f hg => List.isEmpty_iff.mpr (hfn_params_empty_eq key f hg)
  have hdt_params_empty : ∀ key dt, tds.getByKey key = some (.dataType dt) →
      dt.params.isEmpty := fun key dt hg => List.isEmpty_iff.mpr (hdt_params_empty_eq key dt hg)
  -- Typed ctor companion via FnMatchP-class bridge.
  have hctor_companion : ∀ key dt c, tds.getByKey key = some (.constructor dt c) →
      ∃ key', tds.getByKey key' = some (.dataType dt) ∧ c ∈ dt.constructors := by
    intro key dt c hget
    have hP_fn := FnMatchP_checkAndSimplify hdecls hts
    have hsrc_ctor : decls.getByKey key = some (.constructor dt c) :=
      (hP_fn key).2.2 dt c hget
    obtain ⟨hsrc_dt, hcmem⟩ := mkDecls_ctor_companion hdecls key dt c hsrc_ctor
    obtain ⟨dt', htd_dt⟩ := checkAndSimplify_src_dt_to_td hdecls hts hsrc_dt
    have hP := TdDtParamsMatchP_checkAndSimplify hdecls hts
    have hsrc_again : decls.getByKey dt.name = some (.dataType dt') := hP dt.name dt' htd_dt
    have hdt_eq : dt = dt' := by
      rw [hsrc_dt] at hsrc_again
      cases hsrc_again; rfl
    exact ⟨dt.name, hdt_eq ▸ htd_dt, hcmem⟩
  -- Drain preserves AppsReached.
  have hAR : drained.AppsReached tds :=
    concretize_drain_preserves_AppsReached _ _
      (DrainState.AppsReached.init tds hfn_params_empty hdt_params_empty hctor_companion)
      hdrain
  -- Drain preserves SeenSubsetMono.
  have hSSM : drained.SeenSubsetMono :=
    concretize_drain_preserves_SeenSubsetMono _ _
      (DrainState.SeenSubsetMono.init _) hdrain
  -- Drain succeeds → pending empty.
  have hPE : drained.pending.isEmpty :=
    concretize_drain_succeeds_pending_empty _ _ hdrain
  have hPE' : ∀ q, q ∈ drained.pending → False := by
    intro q hq
    have hne : drained.pending.isEmpty = false := by
      rw [Std.HashSet.isEmpty_eq_false_iff_exists_contains_eq_true]
      exact ⟨q, Std.HashSet.contains_iff_mem.mpr hq⟩
    rw [hne] at hPE
    cases hPE
  -- AllAppsP (∈ drained.seen) for each tds-decl type.
  have lift_or : ∀ {t : Typ},
      Typ.AllAppsP (fun g args =>
        (g, args) ∈ drained.seen ∨ (g, args) ∈ drained.pending) t →
      Typ.AllAppsP (fun g args => (g, args) ∈ drained.seen) t := by
    intro t h
    exact h.weaken (fun g args ha => ha.elim id (fun hp => absurd hp (hPE' (g, args))))
  -- Translation: AllAppsP + TypRefsAreDtKeys → TypOkForRewrite.
  have translate : ∀ t, TypRefsAreDtKeys tds t →
      Typ.AllAppsP (fun g args => (g, args) ∈ drained.seen) t →
      TypOkForRewrite drained.mono tds t := by
    intro t hr ha
    exact typOkForRewrite_of_apps_in_seen drained.mono tds drained.seen
      hSSM hdt_params_empty_eq t hr ha
  -- Now assemble the 3 conjuncts.
  obtain ⟨hAR_tds, hAR_dt, hAR_fn⟩ := hAR
  refine ⟨?_, ?_, ?_⟩
  · -- tds-decl types.
    intro key d_src hget
    have hAA := hAR_tds key d_src hget
    have hL1' := hL1 key d_src hget
    cases d_src with
    | function f =>
      simp only at hAA hL1' ⊢
      obtain ⟨hAA_in, hAA_out⟩ := hAA
      obtain ⟨hL1_in, hL1_out⟩ := hL1'
      refine ⟨?_, ?_⟩
      · intro lt hlt
        exact translate lt.snd (hL1_in lt hlt) (lift_or (hAA_in lt hlt))
      · exact translate f.output hL1_out (lift_or hAA_out)
    | dataType dt =>
      simp only at hAA hL1' ⊢
      intro c hc ty hty
      exact translate ty (hL1' c hc ty hty) (lift_or (hAA c hc ty hty))
    | constructor dtc c =>
      simp only at hAA hL1' ⊢
      intro ty hty
      exact translate ty (hL1' ty hty) (lift_or (hAA ty hty))
  · -- drained.newDataTypes — closed via NewDeclTypesRefsOk preservation.
    have hNDT : DrainState.NewDeclTypesRefsOk tds drained :=
      concretize_drain_preserves_NewDeclTypesRefsOk hL1 hfn_params_empty_eq
        hdt_params_empty_eq _ _ (DrainState.NewDeclTypesRefsOk.init _) hdrain
    intro dt hdt c hc ty hty
    exact translate ty (hNDT.1 dt hdt c hc ty hty) (lift_or (hAR_dt dt hdt c hc ty hty))
  · -- drained.newFunctions — closed via NewDeclTypesRefsOk preservation.
    have hNDT : DrainState.NewDeclTypesRefsOk tds drained :=
      concretize_drain_preserves_NewDeclTypesRefsOk hL1 hfn_params_empty_eq
        hdt_params_empty_eq _ _ (DrainState.NewDeclTypesRefsOk.init _) hdrain
    intro f hf
    have hAR_f := hAR_fn f hf
    have hL1_f := hNDT.2 f hf
    refine ⟨?_, ?_⟩
    · intro lt hlt
      exact translate lt.snd (hL1_f.1 lt hlt) (lift_or (hAR_f.1 lt hlt))
    · exact translate f.output hL1_f.2 (lift_or hAR_f.2)

/-- Phase-1 (fromSource) fold preservation on `declTypesNoAppRefDtKey`. -/
theorem concretizeBuild_phase1_preserves_noAppRefDtKey
    (tds : Typed.Decls) (mono : MonoMap)
    (hcover : ∀ key d_src, tds.getByKey key = some d_src →
      match d_src with
      | .function f =>
          (∀ lt ∈ f.inputs, TypOkForRewrite mono tds lt.snd) ∧
          TypOkForRewrite mono tds f.output
      | .dataType dt =>
          ∀ c ∈ dt.constructors, ∀ ty ∈ c.argTypes, TypOkForRewrite mono tds ty
      | .constructor _ c =>
          ∀ ty ∈ c.argTypes, TypOkForRewrite mono tds ty) :
    let emptySubst : Global → Option Typ := fun _ => none
    let fromSource : Typed.Decls := tds.pairs.foldl
      (fun acc p =>
        let (key, d) := p
        match d with
        | .function f =>
          if f.params.isEmpty then
            let newInputs := f.inputs.map fun (l, t) => (l, rewriteTyp emptySubst mono t)
            let newOutput := rewriteTyp emptySubst mono f.output
            let newBody := rewriteTypedTerm tds emptySubst mono f.body
            acc.insert key (.function
              { f with inputs := newInputs, output := newOutput, body := newBody })
          else acc
        | .dataType dt =>
          if dt.params.isEmpty then
            let newCtors := dt.constructors.map fun c =>
              { c with argTypes := c.argTypes.map (rewriteTyp emptySubst mono) }
            acc.insert key (.dataType { dt with constructors := newCtors })
          else acc
        | .constructor dt c =>
          if dt.params.isEmpty then
            let newArgTypes := c.argTypes.map (rewriteTyp emptySubst mono)
            let newCtor : Constructor := { c with argTypes := newArgTypes }
            let rewrittenCtors := dt.constructors.map fun c' =>
              { c' with argTypes := c'.argTypes.map (rewriteTyp emptySubst mono) }
            let newDt : DataType := { dt with constructors := rewrittenCtors }
            acc.insert key (.constructor newDt newCtor)
          else acc)
      default
    ∀ key d_mono, fromSource.getByKey key = some d_mono →
      declTypesNoAppRefDtKey tds d_mono := by
  intro emptySubst fromSource
  let P : Typed.Decls → Prop := fun acc =>
    ∀ key d, acc.getByKey key = some d → declTypesNoAppRefDtKey tds d
  have hinit : P (default : Typed.Decls) := by
    intro key d hget
    rw [default_typedDecls_getByKey_none] at hget
    cases hget
  apply Array.foldl_induction (motive := fun _ acc => P acc) hinit
  intro i acc hP
  have hp_mem : tds.pairs[i.val]'i.isLt ∈ tds.pairs.toList :=
    Array.mem_toList_iff.mpr (Array.getElem_mem _)
  have hget_src_p : tds.getByKey (tds.pairs[i.val]'i.isLt).fst = some (tds.pairs[i.val]'i.isLt).snd := by
    apply IndexMap.getByKey_of_mem_pairs
    exact hp_mem
  have hcover_p := hcover _ _ hget_src_p
  generalize hpr : tds.pairs[i.val]'i.isLt = p at hget_src_p hcover_p hp_mem
  obtain ⟨key, d⟩ := p
  dsimp only at hcover_p
  cases d with
  | function f =>
    obtain ⟨hCi, hCo⟩ := hcover_p
    by_cases hfp : f.params.isEmpty = true
    · simp only [hfp, if_true]
      intro k d_mono hget_mono
      by_cases hkey : (key == k) = true
      · have hkey_eq : key = k := LawfulBEq.eq_of_beq hkey
        subst hkey_eq
        rw [IndexMap.getByKey_insert_self] at hget_mono
        cases hget_mono
        refine ⟨?_, ?_⟩
        · intro lt hlt
          rw [List.mem_map] at hlt
          obtain ⟨lt_src, hlt_src, hlt_eq⟩ := hlt
          rw [← hlt_eq]
          exact rewriteTyp_preserves_TypNoAppRefDtKey lt_src.snd (hCi lt_src hlt_src)
        · exact rewriteTyp_preserves_TypNoAppRefDtKey f.output hCo
      · have hne : (key == k) = false := Bool.not_eq_true _ |>.mp hkey
        rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget_mono
        exact hP k d_mono hget_mono
    · have hfp' : f.params.isEmpty = false := Bool.not_eq_true _ |>.mp hfp
      simp only [hfp']
      exact hP
  | dataType dt =>
    by_cases hdp : dt.params.isEmpty = true
    · simp only [hdp, if_true]
      intro k d_mono hget_mono
      by_cases hkey : (key == k) = true
      · have hkey_eq : key = k := LawfulBEq.eq_of_beq hkey
        subst hkey_eq
        rw [IndexMap.getByKey_insert_self] at hget_mono
        cases hget_mono
        intro c hc ty hty
        rw [List.mem_map] at hc
        obtain ⟨c_src, hc_src, hc_eq⟩ := hc
        rw [← hc_eq] at hty
        dsimp only at hty
        rw [List.mem_map] at hty
        obtain ⟨ty_src, hty_src, hty_eq⟩ := hty
        rw [← hty_eq]
        exact rewriteTyp_preserves_TypNoAppRefDtKey ty_src
          (hcover_p c_src hc_src ty_src hty_src)
      · have hne : (key == k) = false := Bool.not_eq_true _ |>.mp hkey
        rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget_mono
        exact hP k d_mono hget_mono
    · have hdp' : dt.params.isEmpty = false := Bool.not_eq_true _ |>.mp hdp
      simp only [hdp']
      exact hP
  | constructor dtC c =>
    by_cases hcp : dtC.params.isEmpty = true
    · simp only [hcp, if_true]
      intro k d_mono hget_mono
      by_cases hkey : (key == k) = true
      · have hkey_eq : key = k := LawfulBEq.eq_of_beq hkey
        subst hkey_eq
        rw [IndexMap.getByKey_insert_self] at hget_mono
        cases hget_mono
        intro ty hty
        rw [List.mem_map] at hty
        obtain ⟨ty_src, hty_src, hty_eq⟩ := hty
        rw [← hty_eq]
        exact rewriteTyp_preserves_TypNoAppRefDtKey ty_src
          (hcover_p ty_src hty_src)
      · have hne : (key == k) = false := Bool.not_eq_true _ |>.mp hkey
        rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget_mono
        exact hP k d_mono hget_mono
    · have hcp' : dtC.params.isEmpty = false := Bool.not_eq_true _ |>.mp hcp
      simp only [hcp']
      exact hP

/-- Phase-2 (withNewDts) fold preservation on `declTypesNoAppRefDtKey`. -/
theorem concretizeBuild_phase2_preserves_noAppRefDtKey
    (tds : Typed.Decls) (mono : MonoMap)
    (newDataTypes : Array DataType)
    (hcover : ∀ dt ∈ newDataTypes,
      ∀ c ∈ dt.constructors, ∀ ty ∈ c.argTypes, TypOkForRewrite mono tds ty)
    (init : Typed.Decls)
    (hinit : ∀ key d, init.getByKey key = some d → declTypesNoAppRefDtKey tds d) :
    let emptySubst : Global → Option Typ := fun _ => none
    let withNewDts : Typed.Decls := newDataTypes.foldl
      (fun acc dt =>
        let rewrittenCtors := dt.constructors.map fun c =>
          { c with argTypes := c.argTypes.map (rewriteTyp emptySubst mono) }
        let newDt : DataType := { dt with constructors := rewrittenCtors }
        let acc' := acc.insert dt.name (.dataType newDt)
        rewrittenCtors.foldl
          (fun acc'' c =>
            let cName := dt.name.pushNamespace c.nameHead
            acc''.insert cName (.constructor newDt c))
          acc')
      init
    ∀ key d, withNewDts.getByKey key = some d → declTypesNoAppRefDtKey tds d := by
  intro emptySubst withNewDts
  let P : Typed.Decls → Prop := fun acc =>
    ∀ key d, acc.getByKey key = some d → declTypesNoAppRefDtKey tds d
  apply Array.foldl_induction (motive := fun _ acc => P acc) hinit
  intro i acc hP
  let dtOuter := newDataTypes[i.val]'i.isLt
  have hdtOuter_mem : dtOuter ∈ newDataTypes := Array.getElem_mem _
  have hcover_dt := hcover dtOuter hdtOuter_mem
  let rewrittenCtors : List Constructor :=
    dtOuter.constructors.map fun c =>
      ({ c with argTypes := c.argTypes.map (rewriteTyp emptySubst mono) } : Constructor)
  let newDt : DataType := { dtOuter with constructors := rewrittenCtors }
  let acc' := acc.insert dtOuter.name (.dataType newDt)
  have hctor_noapp : ∀ c ∈ rewrittenCtors, ∀ ty ∈ c.argTypes, TypNoAppRefDtKey tds ty := by
    intro c hc_mem ty hty
    rw [List.mem_map] at hc_mem
    obtain ⟨c_src, hc_src, hc_eq⟩ := hc_mem
    rw [← hc_eq] at hty
    dsimp only at hty
    rw [List.mem_map] at hty
    obtain ⟨ty_src, hty_src, hty_eq⟩ := hty
    rw [← hty_eq]
    exact rewriteTyp_preserves_TypNoAppRefDtKey ty_src
      (hcover_dt c_src hc_src ty_src hty_src)
  have hP_acc' : P acc' := by
    intro k d hget
    by_cases hkey : (dtOuter.name == k) = true
    · have hkey_eq : dtOuter.name = k := LawfulBEq.eq_of_beq hkey
      subst hkey_eq
      rw [IndexMap.getByKey_insert_self] at hget
      cases hget
      intro c hc ty hty
      exact hctor_noapp c hc ty hty
    · have hne : (dtOuter.name == k) = false := Bool.not_eq_true _ |>.mp hkey
      rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
      exact hP k d hget
  have hctor_fold_preserves :
      ∀ (cs : List Constructor) (dt : DataType) (init' : Typed.Decls),
        (∀ c ∈ cs, ∀ ty ∈ c.argTypes, TypNoAppRefDtKey tds ty) →
        P init' →
        P (cs.foldl
          (fun acc'' c =>
            let cName := dtOuter.name.pushNamespace c.nameHead
            acc''.insert cName (.constructor dt c))
          init') := by
    intro cs dt init'
    induction cs generalizing init' with
    | nil => intro _ hP'; exact hP'
    | cons c rest ih =>
      intro hall hP'
      simp only [List.foldl_cons]
      have hc_all : ∀ ty ∈ c.argTypes, TypNoAppRefDtKey tds ty :=
        hall c List.mem_cons_self
      have hP_head : P (init'.insert (dtOuter.name.pushNamespace c.nameHead)
          (.constructor dt c)) := by
        intro k d hget
        by_cases hkey : (dtOuter.name.pushNamespace c.nameHead == k) = true
        · have hkey_eq : dtOuter.name.pushNamespace c.nameHead = k :=
            LawfulBEq.eq_of_beq hkey
          subst hkey_eq
          rw [IndexMap.getByKey_insert_self] at hget
          cases hget
          intro ty hty
          exact hc_all ty hty
        · have hne : (dtOuter.name.pushNamespace c.nameHead == k) = false :=
            Bool.not_eq_true _ |>.mp hkey
          rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
          exact hP' k d hget
      exact ih _ (fun c' hc' => hall c' (List.mem_cons_of_mem _ hc')) hP_head
  exact hctor_fold_preserves rewrittenCtors newDt acc' hctor_noapp hP_acc'

/-- Phase-3 (newFunctions) fold preservation on `declTypesNoAppRefDtKey`. -/
theorem concretizeBuild_phase3_preserves_noAppRefDtKey
    (tds : Typed.Decls) (mono : MonoMap)
    (newFunctions : Array Typed.Function)
    (hcover : ∀ f ∈ newFunctions,
      (∀ lt ∈ f.inputs, TypOkForRewrite mono tds lt.snd) ∧
      TypOkForRewrite mono tds f.output)
    (init : Typed.Decls)
    (hinit : ∀ key d, init.getByKey key = some d → declTypesNoAppRefDtKey tds d) :
    let emptySubst : Global → Option Typ := fun _ => none
    let res : Typed.Decls := newFunctions.foldl
      (fun acc f =>
        let newInputs := f.inputs.map fun (l, t) => (l, rewriteTyp emptySubst mono t)
        let newOutput := rewriteTyp emptySubst mono f.output
        let newBody := rewriteTypedTerm tds emptySubst mono f.body
        let newF : Typed.Function :=
          { f with inputs := newInputs, output := newOutput, body := newBody }
        acc.insert f.name (.function newF))
      init
    ∀ key d, res.getByKey key = some d → declTypesNoAppRefDtKey tds d := by
  intro emptySubst res
  let P : Typed.Decls → Prop := fun acc =>
    ∀ key d, acc.getByKey key = some d → declTypesNoAppRefDtKey tds d
  apply Array.foldl_induction (motive := fun _ acc => P acc) hinit
  intro i acc hP
  have hf_mem : newFunctions[i.val]'i.isLt ∈ newFunctions := Array.getElem_mem _
  have hCov := hcover _ hf_mem
  generalize hfeq : newFunctions[i.val]'i.isLt = f at hCov
  obtain ⟨hCi, hCo⟩ := hCov
  intro k d hget
  by_cases hkey : (f.name == k) = true
  · have hkey_eq : f.name = k := LawfulBEq.eq_of_beq hkey
    subst hkey_eq
    rw [IndexMap.getByKey_insert_self] at hget
    cases hget
    refine ⟨?_, ?_⟩
    · intro lt hlt
      rw [List.mem_map] at hlt
      obtain ⟨lt_src, hlt_src, hlt_eq⟩ := hlt
      rw [← hlt_eq]
      exact rewriteTyp_preserves_TypNoAppRefDtKey lt_src.snd (hCi lt_src hlt_src)
    · exact rewriteTyp_preserves_TypNoAppRefDtKey f.output hCo
  · have hne : (f.name == k) = false := Bool.not_eq_true _ |>.mp hkey
    rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
    exact hP k d hget

/-- Main sub-blocker: under FullyMono + checkAndSimplify, every type in
`monoDecls` satisfies `TypNoAppRefDtKey tds`. Decomposes into Layer C
(`rewriteTyp_preserves_TypNoAppRefDtKey`, closed) + Layer A+B
(`drainMono_coversTypesInTds`, the residual). -/
theorem monoDecls_types_noAppRefDtKey
    {t : Source.Toplevel} {tds : Typed.Decls}
    {drained : DrainState}
    (_hmono : FullyMonomorphic t)
    (_hts : t.checkAndSimplify = .ok tds)
    (_hL1 : AllRefsAreDtKeys tds)
    (_hdrain : concretizeDrain tds (concretizeDrainFuel tds)
        { pending := concretizeSeed tds, seen := {}, mono := {},
          newFunctions := #[], newDataTypes := #[] } = .ok drained) :
    let monoDecls : Typed.Decls :=
      concretizeBuild tds drained.mono drained.newFunctions drained.newDataTypes
    ∀ name d_mono, monoDecls.getByKey name = some d_mono →
      declTypesNoAppRefDtKey tds d_mono := by
  intro monoDecls name d_mono hget
  have ⟨hcover_tds, hcover_newDts, hcover_newFns⟩ :=
    drainMono_coversTypesInTds _hmono _hts _hL1 _hdrain
  have hP1 := concretizeBuild_phase1_preserves_noAppRefDtKey tds drained.mono hcover_tds
  have hP2 := concretizeBuild_phase2_preserves_noAppRefDtKey tds drained.mono
    drained.newDataTypes hcover_newDts _ hP1
  have hP3 := concretizeBuild_phase3_preserves_noAppRefDtKey tds drained.mono
    drained.newFunctions hcover_newFns _ hP2
  -- `hP3` produces `declTypesNoAppRefDtKey tds d` from the phase-3 output's getByKey.
  -- Since `monoDecls = concretizeBuild tds drained.mono drained.newFunctions drained.newDataTypes`,
  -- and that equals the phase-3 fold applied to phase-2 applied to phase-1 applied to default,
  -- we apply hP3.
  exact hP3 name d_mono hget

/-- **L3** (body F=1): `AllRefsTargetTds cd tds` modulo
`monoDecls_types_noAppRefDtKey`.

Pipeline: `tds.concretize = .ok cd` unfolds via `concretizeDrain` + fold of
`step4Lower` over `monoDecls.pairs`. The fold invariant
`AllRefsTargetTds · tds` holds on the initial `default` (vacuous) and is
preserved step-wise via `step4Lower_preserves_AllRefsTargetTds`, as long as
every `d_mono` in `monoDecls.pairs` has types satisfying
`TypNoAppRefDtKey tds`. The latter is the single sub-sorry. -/
theorem L3_cd_ref_targets_in_tds
    {t : Source.Toplevel} {tds : Typed.Decls} {cd : Concrete.Decls}
    (hmono : FullyMonomorphic t)
    (hts : t.checkAndSimplify = .ok tds)
    (hconc : tds.concretize = .ok cd)
    (hunique : Typed.Decls.ConcretizeUniqueNames tds)
    (hL1 : AllRefsAreDtKeys tds) :
    AllRefsTargetTds cd tds := by
  have hconc_orig := hconc
  unfold Typed.Decls.concretize at hconc
  simp only [bind, Except.bind] at hconc
  split at hconc
  · cases hconc
  rename_i drained hdrain
  -- `cd = monoDecls.foldlM step4Lower default`.
  have hNoApp : ∀ name d_mono,
      (concretizeBuild tds drained.mono drained.newFunctions drained.newDataTypes).getByKey name
        = some d_mono → declTypesNoAppRefDtKey tds d_mono :=
    monoDecls_types_noAppRefDtKey hmono hts hL1 hdrain
  -- Rewrite `cd`'s defining fold as `List.foldlM` over `monoDecls.pairs.toList`.
  rw [IndexMap.indexMap_foldlM_eq_list_foldlM] at hconc
  -- Pairs satisfy the per-element precondition via `hNoApp`.
  have hpairs : ∀ p ∈ (concretizeBuild tds drained.mono drained.newFunctions
        drained.newDataTypes).pairs.toList,
      declTypesNoAppRefDtKey tds p.snd := by
    intro p hp_mem
    obtain ⟨name, d_mono⟩ := p
    have hget : (concretizeBuild tds drained.mono drained.newFunctions
        drained.newDataTypes).getByKey name = some d_mono :=
      IndexMap.getByKey_of_mem_pairs _ _ _ hp_mem
    exact hNoApp name d_mono hget
  have hinit : AllRefsTargetTds (default : Concrete.Decls) tds := by
    intro key d_cd hget_cd
    rw [show (default : Concrete.Decls).getByKey key = none from by
        unfold IndexMap.getByKey
        show ((default : Concrete.Decls).indices[key]?).bind _ = none
        have : (default : Concrete.Decls).indices[key]? = none := by
          show ((default : Std.HashMap Global Nat))[key]? = none
          exact Std.HashMap.getElem?_empty
        rw [this]; rfl] at hget_cd
    cases hget_cd
  exact step4Lower_foldlM_preserves_AllRefsTargetTds _
    (default : Concrete.Decls) cd hinit hpairs hconc

/-! #### Composition: `RefTargetsInTds → RefClosed` via L2. -/

/-- Every `RefTargetsInTds`-typ lifts to `RefClosed` via L2. Threads the
strengthened L2 hypotheses (`hdt_params_empty`, `hCtorPresent`, `hDtNameIsKey`,
`hNewDtBridge`, `hNewFnBridge`) from the caller, since their discharge lives
downstream in `CheckSound` / `CompilerProgress`. -/
theorem refTargetsInTds_to_refClosed
    {tds : Typed.Decls} {cd : Concrete.Decls}
    (hconc : tds.concretize = .ok cd)
    (hdt_params_empty : ∀ g dt, tds.getByKey g = some (.dataType dt) → dt.params = [])
    (hCtorPresent : ∀ (dtkey : Global) (dt : DataType) (c : Constructor),
      (dtkey, Typed.Declaration.dataType dt) ∈ tds.pairs.toList →
      c ∈ dt.constructors →
      ∃ cc, (dt.name.pushNamespace c.nameHead,
        Typed.Declaration.constructor dt cc) ∈ tds.pairs.toList)
    (hDtNameIsKey : ∀ (key : Global) (dt : DataType),
      (key, Typed.Declaration.dataType dt) ∈ tds.pairs.toList → key = dt.name)
    (hNewDtBridge : ∀ {drained : DrainState},
      concretizeDrain tds (concretizeDrainFuel tds)
          { pending := concretizeSeed tds, seen := {}, mono := {},
            newFunctions := #[], newDataTypes := #[] } = .ok drained →
      NewDtBridge tds drained.newDataTypes)
    (hNewFnBridge : ∀ {drained : DrainState},
      concretizeDrain tds (concretizeDrainFuel tds)
          { pending := concretizeSeed tds, seen := {}, mono := {},
            newFunctions := #[], newDataTypes := #[] } = .ok drained →
      NewFnBridge tds drained.newFunctions)
    {typ : Concrete.Typ}
    (h : RefTargetsInTds tds typ) :
    Concrete.Typ.RefClosed cd typ := by
  induction h with
  | unit => exact .unit
  | field => exact .field
  | pointer _ ih => exact .pointer ih
  | function => exact .function
  | tuple _ ih => exact .tuple ih
  | array _ ih => exact .array ih
  | ref hdt =>
    obtain ⟨dt_tds, hget_tds⟩ := hdt
    obtain ⟨dt_cd, hget_cd⟩ :=
      L2_tds_dtkey_survives_to_cd hconc hdt_params_empty hCtorPresent hDtNameIsKey
        hNewDtBridge hNewFnBridge _ dt_tds hget_tds
    exact .ref ⟨dt_cd, hget_cd⟩

/-! #### Main body. F = 0 (given the 3 L-axioms above). -/

theorem concretize_produces_refClosed
    {t : Source.Toplevel} {tds : Typed.Decls} {cd : Concrete.Decls}
    (_hmono : FullyMonomorphic t)
    (_hts : t.checkAndSimplify = .ok tds)
    (_hconc : tds.concretize = .ok cd)
    (_hunique : Typed.Decls.ConcretizeUniqueNames tds)
    (hdt_params_empty : ∀ g dt, tds.getByKey g = some (.dataType dt) → dt.params = [])
    (hCtorPresent : ∀ (dtkey : Global) (dt : DataType) (c : Constructor),
      (dtkey, Typed.Declaration.dataType dt) ∈ tds.pairs.toList →
      c ∈ dt.constructors →
      ∃ cc, (dt.name.pushNamespace c.nameHead,
        Typed.Declaration.constructor dt cc) ∈ tds.pairs.toList)
    (hDtNameIsKey : ∀ (key : Global) (dt : DataType),
      (key, Typed.Declaration.dataType dt) ∈ tds.pairs.toList → key = dt.name)
    (hNewDtBridge : ∀ {drained : DrainState},
      concretizeDrain tds (concretizeDrainFuel tds)
          { pending := concretizeSeed tds, seen := {}, mono := {},
            newFunctions := #[], newDataTypes := #[] } = .ok drained →
      NewDtBridge tds drained.newDataTypes)
    (hNewFnBridge : ∀ {drained : DrainState},
      concretizeDrain tds (concretizeDrainFuel tds)
          { pending := concretizeSeed tds, seen := {}, mono := {},
            newFunctions := #[], newDataTypes := #[] } = .ok drained →
      NewFnBridge tds drained.newFunctions) :
    Concrete.Decls.RefClosed cd := by
  have hL1 : AllRefsAreDtKeys tds :=
    L1_typed_ref_target_is_tds_dtkey _hmono _hts
  have hL3 : AllRefsTargetTds cd tds :=
    L3_cd_ref_targets_in_tds _hmono _hts _hconc _hunique hL1
  intro name d hget
  have hspec := hL3 name d hget
  match d, hspec with
  | .function f, ⟨hi, ho⟩ =>
    refine ⟨?_, ?_⟩
    · intro lt hlt
      exact refTargetsInTds_to_refClosed _hconc hdt_params_empty hCtorPresent
        hDtNameIsKey hNewDtBridge hNewFnBridge (hi lt hlt)
    · exact refTargetsInTds_to_refClosed _hconc hdt_params_empty hCtorPresent
        hDtNameIsKey hNewDtBridge hNewFnBridge ho
  | .dataType dt, h =>
    intro c hc t ht
    exact refTargetsInTds_to_refClosed _hconc hdt_params_empty hCtorPresent
      hDtNameIsKey hNewDtBridge hNewFnBridge (h c hc t ht)
  | .constructor _ c, h =>
    intro t ht
    exact refTargetsInTds_to_refClosed _hconc hdt_params_empty hCtorPresent
      hDtNameIsKey hNewDtBridge hNewFnBridge (h t ht)

/-- Computational lemma: `concretizeName g #[.ref ⟨.mkSimple s⟩] = g.pushNamespace s`.
Used by hCtorNotKey-discharge to express `g.pushNamespace s` as a concretizeName
output, enabling hUnique application. -/
theorem concretizeName_singleton_ref_simple (g : Global) (s : String) :
    concretizeName g #[.ref ⟨.mkSimple s⟩] = g.pushNamespace s := by
  show #[Typ.ref ⟨.mkSimple s⟩].foldl Typ.appendNameLimbs g = g.pushNamespace s
  show Typ.appendNameLimbs g (.ref ⟨.mkSimple s⟩) = g.pushNamespace s
  rw [Typ.appendNameLimbs.eq_def]
  show Typ.appendNameLimbs.pushAll g (Lean.Name.mkSimple s) = g.pushNamespace s
  rfl

/-- For any `newDt ∈ drained.newDataTypes`, `cd` has SOME entry at `newDt.name`.
Discharged by: `dtStep_inserts_dataType_at_self` produces SOME at newDt.name during
dtStep on newDt; subsequent dtStep / fnStep folds preserve via insert-only;
`step4Lower_fold_kind_at_key` lifts to cd. ORPHAN until reachable via h_cdAt_*. -/
theorem cd_has_some_at_newDt_name
    {tds : Typed.Decls} {drained : DrainState} {cd : Concrete.Decls}
    (hconc' : (concretizeBuild tds drained.mono drained.newFunctions
      drained.newDataTypes).foldlM (init := default) step4Lower = .ok cd)
    {newDt : DataType} (hmem : newDt ∈ drained.newDataTypes) :
    ∃ d, cd.getByKey newDt.name = some d := by
  have hinsert_pres : ∀ (acc : Typed.Decls) (k : Global) (v : Typed.Declaration),
      (∃ d, acc.getByKey newDt.name = some d) →
      ∃ d, (acc.insert k v).getByKey newDt.name = some d := by
    intro acc k v ⟨d, hget⟩
    by_cases hbeq : (k == newDt.name) = true
    · have hkeq : k = newDt.name := LawfulBEq.eq_of_beq hbeq
      rw [hkeq]; exact ⟨v, IndexMap.getByKey_insert_self _ _ _⟩
    · have hne : (k == newDt.name) = false := Bool.not_eq_true _ |>.mp hbeq
      exact ⟨d, by rw [IndexMap.getByKey_insert_of_beq_false _ _ hne]; exact hget⟩
  have hfn_pres : ∀ (acc : Typed.Decls) (f : Typed.Function),
      (∃ d, acc.getByKey newDt.name = some d) →
      ∃ d, (PhaseA2.fnStep tds drained.mono acc f).getByKey newDt.name = some d := by
    intro acc f hacc
    unfold PhaseA2.fnStep
    exact hinsert_pres acc _ _ hacc
  have hdt_inner_pres : ∀ (acc : Typed.Decls) (newDt' : DataType)
      (dt_outer : DataType) (cs : List Constructor),
      (∃ d, acc.getByKey newDt.name = some d) →
      ∃ d, (cs.foldl
        (fun acc'' c =>
          acc''.insert (dt_outer.name.pushNamespace c.nameHead)
            (.constructor newDt' c)) acc).getByKey newDt.name = some d := by
    intro acc newDt' dt_outer cs hacc
    induction cs generalizing acc with
    | nil => exact hacc
    | cons c rest ih =>
      simp only [List.foldl_cons]
      apply ih
      exact hinsert_pres acc _ _ hacc
  have hdt_pres : ∀ (acc : Typed.Decls) (dt' : DataType),
      (∃ d, acc.getByKey newDt.name = some d) →
      ∃ d, (PhaseA2.dtStep drained.mono acc dt').getByKey newDt.name = some d := by
    intro acc dt' hacc
    simp only [PhaseA2.dtStep]
    apply hdt_inner_pres
    exact hinsert_pres acc _ _ hacc
  have hdt_list_fold_pres : ∀ (l : List DataType) (init : Typed.Decls),
      (∃ d, init.getByKey newDt.name = some d) →
      ∃ d, (l.foldl (PhaseA2.dtStep drained.mono) init).getByKey newDt.name = some d := by
    intro l
    induction l with
    | nil => intro init h; exact h
    | cons hd rest ih =>
      intro init h
      simp only [List.foldl_cons]
      exact ih _ (hdt_pres _ hd h)
  have hfn_list_fold_pres : ∀ (l : List Typed.Function) (init : Typed.Decls),
      (∃ d, init.getByKey newDt.name = some d) →
      ∃ d, (l.foldl (PhaseA2.fnStep tds drained.mono) init).getByKey newDt.name = some d := by
    intro l
    induction l with
    | nil => intro init h; exact h
    | cons hd rest ih =>
      intro init h
      simp only [List.foldl_cons]
      exact ih _ (hfn_pres _ hd h)
  have hmono_some : ∃ d, (concretizeBuild tds drained.mono drained.newFunctions
      drained.newDataTypes).getByKey newDt.name = some d := by
    rw [PhaseA2.concretizeBuild_eq]
    obtain ⟨pre, post, hsplit⟩ :=
      List.append_of_mem (Array.mem_toList_iff.mpr hmem)
    rw [show (drained.newDataTypes.foldl (PhaseA2.dtStep drained.mono)
          (tds.pairs.foldl (PhaseA2.srcStep tds drained.mono) default))
        = (drained.newDataTypes.toList.foldl (PhaseA2.dtStep drained.mono)
            (tds.pairs.foldl (PhaseA2.srcStep tds drained.mono) default))
        from by rw [← Array.foldl_toList]]
    rw [show (drained.newFunctions.foldl (PhaseA2.fnStep tds drained.mono) _)
        = (drained.newFunctions.toList.foldl (PhaseA2.fnStep tds drained.mono) _)
        from by rw [← Array.foldl_toList]]
    rw [hsplit, List.foldl_append, List.foldl_cons]
    have h_dtstep_some :
        ∃ d, (PhaseA2.dtStep drained.mono
          (pre.foldl (PhaseA2.dtStep drained.mono)
            (tds.pairs.foldl (PhaseA2.srcStep tds drained.mono) default))
          newDt).getByKey newDt.name = some d := by
      obtain ⟨md_dt, hmd⟩ :=
        PhaseA2.dtStep_inserts_dataType_at_self drained.mono _ newDt
      exact ⟨_, hmd⟩
    exact hfn_list_fold_pres _ _ (hdt_list_fold_pres post _ h_dtstep_some)
  obtain ⟨d_mono, hmono_get⟩ := hmono_some
  have h_kind := step4Lower_fold_kind_at_key hmono_get hconc'
  cases d_mono with
  | function _ => obtain ⟨cf, hcf⟩ := h_kind; exact ⟨_, hcf⟩
  | dataType _ => obtain ⟨cdt', hcdt'⟩ := h_kind; exact ⟨_, hcdt'⟩
  | constructor _ _ => obtain ⟨cdt', cc, hcc⟩ := h_kind; exact ⟨_, hcc⟩

/-- For any `newDt ∈ drained.newDataTypes` and `c ∈ newDt.constructors`,
`cd` has SOME entry at `newDt.name.pushNamespace c.nameHead`.

dtStep on newDt's inner ctor-fold inserts a `.constructor` at this key
(via `dtStep_inserts_ctor_at_self_ctor`); subsequent dtStep / fnStep folds
preserve via insert-only; `step4Lower_fold_kind_at_key` lifts to cd. -/
theorem cd_has_some_at_newDt_ctor_name
    {tds : Typed.Decls} {drained : DrainState} {cd : Concrete.Decls}
    (hconc' : (concretizeBuild tds drained.mono drained.newFunctions
      drained.newDataTypes).foldlM (init := default) step4Lower = .ok cd)
    {newDt : DataType} (hmem : newDt ∈ drained.newDataTypes)
    {c : Constructor} (hc : c ∈ newDt.constructors) :
    ∃ d, cd.getByKey (newDt.name.pushNamespace c.nameHead) = some d := by
  let pushedKey : Global := newDt.name.pushNamespace c.nameHead
  have hinsert_pres : ∀ (acc : Typed.Decls) (k : Global) (v : Typed.Declaration),
      (∃ d, acc.getByKey pushedKey = some d) →
      ∃ d, (acc.insert k v).getByKey pushedKey = some d := by
    intro acc k v ⟨d, hget⟩
    by_cases hbeq : (k == pushedKey) = true
    · have hkeq : k = pushedKey := LawfulBEq.eq_of_beq hbeq
      rw [hkeq]; exact ⟨v, IndexMap.getByKey_insert_self _ _ _⟩
    · have hne : (k == pushedKey) = false := Bool.not_eq_true _ |>.mp hbeq
      exact ⟨d, by rw [IndexMap.getByKey_insert_of_beq_false _ _ hne]; exact hget⟩
  have hfn_pres : ∀ (acc : Typed.Decls) (f : Typed.Function),
      (∃ d, acc.getByKey pushedKey = some d) →
      ∃ d, (PhaseA2.fnStep tds drained.mono acc f).getByKey pushedKey = some d := by
    intro acc f hacc
    unfold PhaseA2.fnStep
    exact hinsert_pres acc _ _ hacc
  have hdt_inner_pres : ∀ (acc : Typed.Decls) (newDt' : DataType)
      (dt_outer : DataType) (cs : List Constructor),
      (∃ d, acc.getByKey pushedKey = some d) →
      ∃ d, (cs.foldl
        (fun acc'' c =>
          acc''.insert (dt_outer.name.pushNamespace c.nameHead)
            (.constructor newDt' c)) acc).getByKey pushedKey = some d := by
    intro acc newDt' dt_outer cs hacc
    induction cs generalizing acc with
    | nil => exact hacc
    | cons c rest ih =>
      simp only [List.foldl_cons]
      apply ih
      exact hinsert_pres acc _ _ hacc
  have hdt_pres : ∀ (acc : Typed.Decls) (dt' : DataType),
      (∃ d, acc.getByKey pushedKey = some d) →
      ∃ d, (PhaseA2.dtStep drained.mono acc dt').getByKey pushedKey = some d := by
    intro acc dt' hacc
    simp only [PhaseA2.dtStep]
    apply hdt_inner_pres
    exact hinsert_pres acc _ _ hacc
  have hdt_list_fold_pres : ∀ (l : List DataType) (init : Typed.Decls),
      (∃ d, init.getByKey pushedKey = some d) →
      ∃ d, (l.foldl (PhaseA2.dtStep drained.mono) init).getByKey pushedKey = some d := by
    intro l
    induction l with
    | nil => intro init h; exact h
    | cons hd rest ih =>
      intro init h
      simp only [List.foldl_cons]
      exact ih _ (hdt_pres _ hd h)
  have hfn_list_fold_pres : ∀ (l : List Typed.Function) (init : Typed.Decls),
      (∃ d, init.getByKey pushedKey = some d) →
      ∃ d, (l.foldl (PhaseA2.fnStep tds drained.mono) init).getByKey pushedKey = some d := by
    intro l
    induction l with
    | nil => intro init h; exact h
    | cons hd rest ih =>
      intro init h
      simp only [List.foldl_cons]
      exact ih _ (hfn_pres _ hd h)
  have hmono_some : ∃ d, (concretizeBuild tds drained.mono drained.newFunctions
      drained.newDataTypes).getByKey pushedKey = some d := by
    rw [PhaseA2.concretizeBuild_eq]
    obtain ⟨pre, post, hsplit⟩ :=
      List.append_of_mem (Array.mem_toList_iff.mpr hmem)
    rw [show (drained.newDataTypes.foldl (PhaseA2.dtStep drained.mono)
          (tds.pairs.foldl (PhaseA2.srcStep tds drained.mono) default))
        = (drained.newDataTypes.toList.foldl (PhaseA2.dtStep drained.mono)
            (tds.pairs.foldl (PhaseA2.srcStep tds drained.mono) default))
        from by rw [← Array.foldl_toList]]
    rw [show (drained.newFunctions.foldl (PhaseA2.fnStep tds drained.mono) _)
        = (drained.newFunctions.toList.foldl (PhaseA2.fnStep tds drained.mono) _)
        from by rw [← Array.foldl_toList]]
    rw [hsplit, List.foldl_append, List.foldl_cons]
    have h_dtstep_some :
        ∃ d, (PhaseA2.dtStep drained.mono
          (pre.foldl (PhaseA2.dtStep drained.mono)
            (tds.pairs.foldl (PhaseA2.srcStep tds drained.mono) default))
          newDt).getByKey pushedKey = some d := by
      obtain ⟨md_dt, md_c, hget⟩ :=
        PhaseA2.dtStep_inserts_ctor_at_self_ctor drained.mono _ newDt hc
      exact ⟨_, hget⟩
    exact hfn_list_fold_pres _ _ (hdt_list_fold_pres post _ h_dtstep_some)
  obtain ⟨d_mono, hmono_get⟩ := hmono_some
  have h_kind := step4Lower_fold_kind_at_key hmono_get hconc'
  cases d_mono with
  | function _ => obtain ⟨cf, hcf⟩ := h_kind; exact ⟨_, hcf⟩
  | dataType _ => obtain ⟨cdt', hcdt'⟩ := h_kind; exact ⟨_, hcdt'⟩
  | constructor _ _ => obtain ⟨cdt', cc, hcc⟩ := h_kind; exact ⟨_, hcc⟩

end RefClosedBody

/-! ### `CtorArgsAppRefToDt` drain invariant chain.

Companion to `PendingArgsAppRefToDt`: every `dt ∈ st.newDataTypes` and
`c ∈ dt.constructors` has `c.argTypes` consisting of `AppRefToDt tds`-safe
types. Discharges `BLOCKED-A.1-{ctor,fn}-md_AR-newDt` sorries in
`Toplevel.concretize_produces_refClosed_entry` by giving each new dt's ctor
argTypes the `AppRefToDt tds`-shape needed to lift to `AppRefToDtOrNewDt`
via `rewriteTyp_preserves_AppRefToDtOrNewDt`.

The `DrainState.X` and `Typed.Decls.AllCtorArgsAppRefToDt` definitions live
at the top-level `Aiur` namespace (so dot-notation `state.X` resolves to
`Aiur.DrainState.X`); the helper lemmas and chain proofs are scoped under
`RefClosedBody` (reopened below) since they cite `RefClosedBody` lemmas. -/

/-- Every `(g, args) ∈ st.pending` has all `args` AppRefToDt-safe (post-
instantiate context: `params = []`). -/
def DrainState.PendingArgsAppRefToDt (tds : Typed.Decls) (st : DrainState) : Prop :=
  ∀ (entry : Global × Array Typ), entry ∈ st.pending →
    ∀ t ∈ entry.2, Typed.Typ.AppRefToDt tds [] t

/-- Every `dt ∈ st.newDataTypes` and `c ∈ dt.constructors` has `c.argTypes`
AppRefToDt-safe (post-instantiate context). -/
def DrainState.CtorArgsAppRefToDt (tds : Typed.Decls) (st : DrainState) : Prop :=
  ∀ dt ∈ st.newDataTypes, ∀ c ∈ dt.constructors, ∀ t ∈ c.argTypes,
    Typed.Typ.AppRefToDt tds [] t

/-- Source-side precondition: every tds dt-key has AppRefToDt-safe ctor argTypes
under the dt's own type-parameter context. -/
def Typed.Decls.AllCtorArgsAppRefToDt (tds : Typed.Decls) : Prop :=
  ∀ g dt c, tds.getByKey g = some (.dataType dt) → c ∈ dt.constructors →
    ∀ t ∈ c.argTypes, Typed.Typ.AppRefToDt tds dt.params t

/-- Every `f ∈ st.newFunctions` has all input snd's AppRefToDt-safe. -/
def DrainState.NewFnInputsAppRefToDt (tds : Typed.Decls) (st : DrainState) : Prop :=
  ∀ f ∈ st.newFunctions, ∀ (lt : Local × Typ), lt ∈ f.inputs →
    Typed.Typ.AppRefToDt tds [] lt.2

/-- Every `f ∈ st.newFunctions` has output AppRefToDt-safe. -/
def DrainState.NewFnOutputAppRefToDt (tds : Typed.Decls) (st : DrainState) : Prop :=
  ∀ f ∈ st.newFunctions, Typed.Typ.AppRefToDt tds [] f.output

/-- Source-side precondition: every tds fn-key has AppRefToDt-safe input snd's
under the fn's own type-parameter context. -/
def Typed.Decls.AllFnInputsAppRefToDt (tds : Typed.Decls) : Prop :=
  ∀ g f, tds.getByKey g = some (.function f) →
    ∀ (lt : Local × Typ), lt ∈ f.inputs →
      Typed.Typ.AppRefToDt tds f.params lt.2

/-- Source-side precondition: every tds fn-key has AppRefToDt-safe output
under the fn's own type-parameter context. -/
def Typed.Decls.AllFnOutputAppRefToDt (tds : Typed.Decls) : Prop :=
  ∀ g f, tds.getByKey g = some (.function f) →
    Typed.Typ.AppRefToDt tds f.params f.output

/-! ## `Typed.Decls.AllAppRefToDt` — broad source-side AppRefToDt invariant.

Sig amendment 2026-05-03 (Invariant 3, Defect 3): broader source-side
invariant covering every position the seed touches. The previous narrow
`AllCtorArgsAppRefToDt` premise was insufficient for
`PendingArgsAppRefToDt.init` because `concretizeSeed` traverses BOTH
function bodies (output, inputs, body-term, call-site type args) AND
ctor argTypes, so the seed can produce `pending` entries with `tArgs`
sourced from any of those positions.

`AllAppRefToDt` bundles the four narrower predicates already defined
above (`AllCtorArgsAppRefToDt + AllFnInputsAppRefToDt +
AllFnOutputAppRefToDt`) plus a body-position invariant
`AllFnBodyAppRefToDt` covering `Typ` annotations inside function bodies.
The bundled form is the right hypothesis for `init`; producers at the
caller (`concretize_produces_PendingArgsAppRefToDt`) discharge it from
`WellFormed`-derived per-position witnesses (each is already F=0 in
this file via `*_of_wellFormed`). -/

-- `Typed.Term.AppRefToDt` moved upstream to
-- `Ix/Aiur/Semantics/WellFormed.lean` (2026-05-04). Downstream consumers
-- in this file reference it via fully qualified name `Typed.Term.AppRefToDt`.

-- The full inductive arms (`unit, var, ref, field, tuple, array, ret, let,
-- match, app, add, sub, mul, eqZero, proj, get, slice, set, store, load,
-- ptrVal, assertEq, ioGetInfo, ioSetInfo, ioRead, ioWrite, u8*, u32*, debug`)
-- are now defined in WellFormed.lean.

/-- Body-position invariant for the seed: every function body satisfies
`Typed.Term.AppRefToDt tds f.params f.body`. Captures the body-position
cluster that `collectInTypedTerm` and `collectCalls` traverse during
`concretizeSeed`. Mirrors `Typed.Term.AppRefTArgsFO`'s decls-level
quantifier in `Typed.Decls.AppRefTArgsFO`. -/
def Typed.Decls.AllFnBodyAppRefToDt (tds : Typed.Decls) : Prop :=
  ∀ g f, tds.getByKey g = some (.function f) →
    Typed.Term.AppRefToDt tds f.params f.body

/-- Bundled source-side AppRefToDt invariant covering all seed-traversed
positions (function output, inputs, body, ctor argTypes). Replaces the
narrow `AllCtorArgsAppRefToDt` consumed by `PendingArgsAppRefToDt.init`. -/
def Typed.Decls.AllAppRefToDt (tds : Typed.Decls) : Prop :=
  Typed.Decls.AllCtorArgsAppRefToDt tds ∧
  Typed.Decls.AllFnInputsAppRefToDt tds ∧
  Typed.Decls.AllFnOutputAppRefToDt tds ∧
  Typed.Decls.AllFnBodyAppRefToDt tds

namespace RefClosedBody

/-! #### Helper lemmas: `Typ.instantiate` and `collectInTyp`/`collectInTypedTerm`/
`collectCalls` preserve `AppRefToDt`. -/

/-- `Typ.instantiate` lifts `Typed.Typ.AppRefToDt tds P_in t` to
`Typed.Typ.AppRefToDt tds P_out (instantiate subst t)`, given:
* `hsubst`: the substitution maps every name (when defined) to a
  `P_out`-AppRefToDt-safe type.
* `hsubst_total`: the substitution is total on `P_in`'s type-parameter names
  — every `g` of the structural form `Global.init p` for some `p ∈ P_in` has
  `subst g = some _`.

Used in `concretizeDrainEntry_preserves_*` where `P_in = dt.params/f.params`
(the template's parameter list) and `P_out = []` (the post-instantiate
context); `mkParamSubst dt.params entry.2` with `entry.2.size = dt.params.length`
satisfies `hsubst_total` (see `mkParamSubst_total_on_params`). Mirrors
`Typ.instantiate_preserves_AppRefTArgsFO` (FirstOrder.lean:911). -/
theorem Typ.instantiate_preserves_AppRefToDt
    (subst : Global → Option Typ) {tds : Typed.Decls}
    {P_in P_out : List String} {t : Typ}
    (hsubst : ∀ g t', subst g = some t' → Typed.Typ.AppRefToDt tds P_out t')
    (hsubst_total : ∀ g, (∃ p ∈ P_in, g = Global.init p) →
      ∃ t', subst g = some t')
    (hAR : Typed.Typ.AppRefToDt tds P_in t) :
    Typed.Typ.AppRefToDt tds P_out (Typ.instantiate subst t) := by
  induction hAR with
  | unit => unfold Typ.instantiate; exact .unit
  | field => unfold Typ.instantiate; exact .field
  | mvar n => unfold Typ.instantiate; exact .mvar n
  | @ref g hdt =>
    unfold Typ.instantiate
    cases hsub : subst g with
    | none => simp only [hsub, Option.getD_none]; exact .ref hdt
    | some t' =>
      simp only [hsub, Option.getD_some]
      exact hsubst g t' hsub
  | @refTypeParam g hin =>
    unfold Typ.instantiate
    obtain ⟨t', ht'⟩ := hsubst_total g hin
    rw [ht']
    simp only [Option.getD_some]
    exact hsubst g t' ht'
  | @tuple ts _ ih =>
    unfold Typ.instantiate
    refine .tuple ?_
    intro t' ht'
    obtain ⟨t0, ht0mem, ht0eq⟩ := mem_of_attach_map ts _ ht'
    subst ht0eq
    exact ih t0 ht0mem
  | @array t n _ iht =>
    unfold Typ.instantiate
    exact .array iht
  | @pointer t _ iht =>
    unfold Typ.instantiate
    exact .pointer iht
  | @app g args hdt _ ih =>
    unfold Typ.instantiate
    refine .app hdt ?_
    intro t' ht'
    obtain ⟨t0, ht0mem, ht0eq⟩ := mem_of_attach_map args _ ht'
    subst ht0eq
    exact ih t0 ht0mem
  | @function ins out _ _ ih_ins ih_out =>
    unfold Typ.instantiate
    refine .function ?_ ih_out
    intro t' ht'
    obtain ⟨t0, ht0mem, ht0eq⟩ := list_mem_of_attach_map ins _ ht'
    subst ht0eq
    exact ih_ins t0 ht0mem

/-- `collectInTyp` preserves the AppRefToDt-pending invariant: under
`AppRefToDt tds [] τ` and `seen` carrying AppRefToDt args, every collected entry
carries AppRefToDt args. Mirrors `collectInTyp_PendingArgsFO_step`
(FirstOrder.lean:963). Specialised to the post-instantiate context (`params = []`). -/
theorem collectInTyp_preserves_AppRefToDt {tds : Typed.Decls} {τ : Typ}
    (hAR : Typed.Typ.AppRefToDt tds [] τ) :
    ∀ (seen : Std.HashSet (Global × Array Typ)),
      (∀ entry ∈ seen, ∀ t ∈ entry.2, Typed.Typ.AppRefToDt tds [] t) →
      ∀ entry ∈ collectInTyp seen τ, ∀ t ∈ entry.2,
        Typed.Typ.AppRefToDt tds [] t := by
  induction hAR with
  | unit => intro seen hseen; unfold collectInTyp; exact hseen
  | field => intro seen hseen; unfold collectInTyp; exact hseen
  | mvar n => intro seen hseen; unfold collectInTyp; exact hseen
  | ref g => intro seen hseen; unfold collectInTyp; exact hseen
  | @refTypeParam g hin =>
    -- params = [] ⇒ vacuous.
    exact absurd hin (by simp)
  | @tuple ts _h ih =>
    intro seen hseen
    unfold collectInTyp
    apply Array.foldl_induction
      (motive := fun (_ : Nat) (acc : Std.HashSet (Global × Array Typ)) =>
        ∀ entry ∈ acc, ∀ t ∈ entry.2, Typed.Typ.AppRefToDt tds [] t) hseen
    intro i acc hinv
    obtain ⟨t, ht⟩ := ts.attach[i.val]'i.isLt
    exact ih t ht acc hinv
  | @array t n _ iht =>
    intro seen hseen
    unfold collectInTyp
    exact iht seen hseen
  | @pointer t _ iht =>
    intro seen hseen
    unfold collectInTyp
    exact iht seen hseen
  | @app g args hdt hargsRec ih =>
    intro seen hseen
    unfold collectInTyp
    have hafter : ∀ entry ∈ args.attach.foldl
        (fun s ⟨t, _⟩ => collectInTyp s t) seen,
        ∀ t ∈ entry.2, Typed.Typ.AppRefToDt tds [] t := by
      apply Array.foldl_induction
        (motive := fun (_ : Nat) (acc : Std.HashSet (Global × Array Typ)) =>
          ∀ entry ∈ acc, ∀ t ∈ entry.2, Typed.Typ.AppRefToDt tds [] t) hseen
      intro i acc hinv
      obtain ⟨t, ht⟩ := args.attach[i.val]'i.isLt
      exact ih t ht acc hinv
    intro entry hent t ht
    rcases Std.HashSet.mem_insert.mp hent with hbeq | hin
    · -- (g, args) == entry: entry = (g, args), so t ∈ args is AppRefToDt by hargsRec.
      have hpair : (g, args) = entry := LawfulBEq.eq_of_beq hbeq
      rw [← hpair] at ht
      exact hargsRec t ht
    · exact hafter entry hin t ht
  | @function ins out _h_ins _h_out ih_ins ih_out =>
    intro seen hseen
    unfold collectInTyp
    have hafter_ins : ∀ entry ∈ ins.attach.foldl
        (fun s ⟨t, _⟩ => collectInTyp s t) seen,
        ∀ t' ∈ entry.2, Typed.Typ.AppRefToDt tds [] t' := by
      have aux : ∀ (l : List {x // x ∈ ins})
          (acc : Std.HashSet (Global × Array Typ)),
          (∀ entry ∈ acc, ∀ t' ∈ entry.2, Typed.Typ.AppRefToDt tds [] t') →
          ∀ entry ∈ l.foldl (fun s ⟨t, _⟩ => collectInTyp s t) acc,
            ∀ t' ∈ entry.2, Typed.Typ.AppRefToDt tds [] t' := by
        intro l
        induction l with
        | nil => intro acc hacc entry hent; exact hacc entry hent
        | cons hd tl ih_l =>
          intro acc hacc
          simp only [List.foldl_cons]
          apply ih_l
          obtain ⟨t, ht⟩ := hd
          exact ih_ins t ht acc hacc
      exact aux ins.attach seen hseen
    exact ih_out _ hafter_ins

/-- `collectInTypedTerm` preserves the AppRefToDt-pending invariant. Mirrors
`collectInTypedTerm_PendingArgsFO_step` (FirstOrder.lean:1034). Specialised
to `params = []`. -/
theorem collectInTypedTerm_preserves_AppRefToDt {tds : Typed.Decls}
    {term : Typed.Term} (hAR : Typed.Term.AppRefToDt tds [] term) :
    ∀ (seen : Std.HashSet (Global × Array Typ)),
      (∀ entry ∈ seen, ∀ t ∈ entry.2, Typed.Typ.AppRefToDt tds [] t) →
      ∀ entry ∈ collectInTypedTerm seen term, ∀ t ∈ entry.2,
        Typed.Typ.AppRefToDt tds [] t := by
  induction hAR with
  | unit htyp => intro seen hseen; unfold collectInTypedTerm
                 exact collectInTyp_preserves_AppRefToDt htyp seen hseen
  | var htyp => intro seen hseen; unfold collectInTypedTerm
                exact collectInTyp_preserves_AppRefToDt htyp seen hseen
  | @ref typ e g tArgs htyp hArgs =>
    intro seen hseen
    unfold collectInTypedTerm
    have h_typ := collectInTyp_preserves_AppRefToDt htyp seen hseen
    apply Array.foldl_induction
      (motive := fun (_ : Nat) (acc : Std.HashSet (Global × Array Typ)) =>
        ∀ entry ∈ acc, ∀ t ∈ entry.2, Typed.Typ.AppRefToDt tds [] t) h_typ
    intro i acc hinv
    have hti : Typed.Typ.AppRefToDt tds [] (tArgs[i.val]'i.isLt) :=
      hArgs _ (Array.getElem_mem _)
    exact collectInTyp_preserves_AppRefToDt hti acc hinv
  | field htyp => intro seen hseen; unfold collectInTypedTerm
                  exact collectInTyp_preserves_AppRefToDt htyp seen hseen
  | @tuple typ e ts htyp _h ih =>
    intro seen hseen
    unfold collectInTypedTerm
    have h_typ := collectInTyp_preserves_AppRefToDt htyp seen hseen
    apply Array.foldl_induction
      (motive := fun (_ : Nat) (acc : Std.HashSet (Global × Array Typ)) =>
        ∀ entry ∈ acc, ∀ t ∈ entry.2, Typed.Typ.AppRefToDt tds [] t) h_typ
    intro i acc hinv
    obtain ⟨t, ht⟩ := ts.attach[i.val]'i.isLt
    exact ih t ht acc hinv
  | @array typ e ts htyp _h ih =>
    intro seen hseen
    unfold collectInTypedTerm
    have h_typ := collectInTyp_preserves_AppRefToDt htyp seen hseen
    apply Array.foldl_induction
      (motive := fun (_ : Nat) (acc : Std.HashSet (Global × Array Typ)) =>
        ∀ entry ∈ acc, ∀ t ∈ entry.2, Typed.Typ.AppRefToDt tds [] t) h_typ
    intro i acc hinv
    obtain ⟨t, ht⟩ := ts.attach[i.val]'i.isLt
    exact ih t ht acc hinv
  | @ret typ e sub htyp _h ih =>
    intro seen hseen
    unfold collectInTypedTerm
    exact ih _ (collectInTyp_preserves_AppRefToDt htyp seen hseen)
  | @«let» typ e pat v b htyp _hv _hb ihv ihb =>
    intro seen hseen
    unfold collectInTypedTerm
    exact ihb _ (ihv _ (collectInTyp_preserves_AppRefToDt htyp seen hseen))
  | @«match» typ e scrut cases htyp _hscrut _hcases ihscrut ih_cases =>
    intro seen hseen
    unfold collectInTypedTerm
    have h_typ := collectInTyp_preserves_AppRefToDt htyp seen hseen
    have h_scrut := ihscrut _ h_typ
    have aux : ∀ (l : List {x // x ∈ cases})
        (acc : Std.HashSet (Global × Array Typ)),
        (∀ entry ∈ acc, ∀ t' ∈ entry.2, Typed.Typ.AppRefToDt tds [] t') →
        ∀ entry ∈ l.foldl
          (fun s x => match x with | ⟨(_, b), _⟩ => collectInTypedTerm s b) acc,
          ∀ t' ∈ entry.2, Typed.Typ.AppRefToDt tds [] t' := by
      intro l
      induction l with
      | nil => intro acc hacc entry hent; exact hacc entry hent
      | cons hd tl ih_l =>
        intro acc hacc
        simp only [List.foldl_cons]
        apply ih_l
        obtain ⟨pc, hpc⟩ := hd
        obtain ⟨pat, b⟩ := pc
        exact ih_cases ⟨pat, b⟩ hpc acc hacc
    exact aux cases.attach _ h_scrut
  | @app typ e g tArgs args u htyp hArgs _hargs ihargs =>
    intro seen hseen
    unfold collectInTypedTerm
    have h_typ := collectInTyp_preserves_AppRefToDt htyp seen hseen
    have h_tArgs : ∀ entry ∈ tArgs.foldl collectInTyp (collectInTyp seen typ),
        ∀ t ∈ entry.2, Typed.Typ.AppRefToDt tds [] t := by
      apply Array.foldl_induction
        (motive := fun (_ : Nat) (acc : Std.HashSet (Global × Array Typ)) =>
          ∀ entry ∈ acc, ∀ t ∈ entry.2, Typed.Typ.AppRefToDt tds [] t) h_typ
      intro i acc hinv
      have hti : Typed.Typ.AppRefToDt tds [] (tArgs[i.val]'i.isLt) :=
        hArgs _ (Array.getElem_mem _)
      exact collectInTyp_preserves_AppRefToDt hti acc hinv
    have aux : ∀ (l : List {x // x ∈ args})
        (acc : Std.HashSet (Global × Array Typ)),
        (∀ entry ∈ acc, ∀ t' ∈ entry.2, Typed.Typ.AppRefToDt tds [] t') →
        ∀ entry ∈ l.foldl (fun s ⟨a, _⟩ => collectInTypedTerm s a) acc,
          ∀ t' ∈ entry.2, Typed.Typ.AppRefToDt tds [] t' := by
      intro l
      induction l with
      | nil => intro acc hacc entry hent; exact hacc entry hent
      | cons hd tl ih_l =>
        intro acc hacc
        simp only [List.foldl_cons]
        apply ih_l
        obtain ⟨a, ha⟩ := hd
        exact ihargs a ha acc hacc
    exact aux args.attach _ h_tArgs
  | @add typ e a b htyp _ha _hb iha ihb | @sub typ e a b htyp _ha _hb iha ihb
  | @mul typ e a b htyp _ha _hb iha ihb | @u8Xor typ e a b htyp _ha _hb iha ihb
  | @u8Add typ e a b htyp _ha _hb iha ihb | @u8Sub typ e a b htyp _ha _hb iha ihb
  | @u8And typ e a b htyp _ha _hb iha ihb | @u8Or typ e a b htyp _ha _hb iha ihb
  | @u8LessThan typ e a b htyp _ha _hb iha ihb
  | @u32LessThan typ e a b htyp _ha _hb iha ihb =>
    intro seen hseen
    unfold collectInTypedTerm
    exact ihb _ (iha _ (collectInTyp_preserves_AppRefToDt htyp seen hseen))
  | @eqZero typ e a htyp _ha iha | @store typ e a htyp _ha iha
  | @load typ e a htyp _ha iha | @ptrVal typ e a htyp _ha iha
  | @u8BitDecomposition typ e a htyp _ha iha
  | @u8ShiftLeft typ e a htyp _ha iha | @u8ShiftRight typ e a htyp _ha iha
  | @ioGetInfo typ e a htyp _ha iha =>
    intro seen hseen
    unfold collectInTypedTerm
    exact iha _ (collectInTyp_preserves_AppRefToDt htyp seen hseen)
  | @proj typ e a n htyp _ha iha | @get typ e a n htyp _ha iha =>
    intro seen hseen
    unfold collectInTypedTerm
    exact iha _ (collectInTyp_preserves_AppRefToDt htyp seen hseen)
  | @slice typ e a i j htyp _ha iha =>
    intro seen hseen
    unfold collectInTypedTerm
    exact iha _ (collectInTyp_preserves_AppRefToDt htyp seen hseen)
  | @«set» typ e a n v htyp _ha _hv iha ihv =>
    intro seen hseen
    unfold collectInTypedTerm
    exact ihv _ (iha _ (collectInTyp_preserves_AppRefToDt htyp seen hseen))
  | @assertEq typ e a b r htyp _ha _hb _hr iha ihb ihr =>
    intro seen hseen
    unfold collectInTypedTerm
    exact ihr _ (ihb _ (iha _ (collectInTyp_preserves_AppRefToDt htyp seen hseen)))
  | @ioSetInfo typ e k i l r htyp _hk _hi _hl _hr ihk ihi ihl ihr =>
    intro seen hseen
    unfold collectInTypedTerm
    exact ihr _ (ihl _ (ihi _ (ihk _ (collectInTyp_preserves_AppRefToDt htyp seen hseen))))
  | @ioRead typ e i n htyp _hi ihi =>
    intro seen hseen
    unfold collectInTypedTerm
    exact ihi _ (collectInTyp_preserves_AppRefToDt htyp seen hseen)
  | @ioWrite typ e d r htyp _hd _hr ihd ihr =>
    intro seen hseen
    unfold collectInTypedTerm
    exact ihr _ (ihd _ (collectInTyp_preserves_AppRefToDt htyp seen hseen))
  | @debug typ e label t r htyp _ht _hr iht ihr =>
    intro seen hseen
    unfold collectInTypedTerm
    have h_typ := collectInTyp_preserves_AppRefToDt htyp seen hseen
    have h_t : ∀ entry ∈ (match t with
                          | some t => collectInTypedTerm (collectInTyp seen typ) t
                          | none => collectInTyp seen typ),
        ∀ t' ∈ entry.2, Typed.Typ.AppRefToDt tds [] t' := by
      cases t with
      | none => exact h_typ
      | some tval => exact iht tval rfl _ h_typ
    exact ihr _ h_t

/-- `collectCalls` preserves the AppRefToDt-pending invariant. Mirrors
`collectCalls_PendingArgsFO_step` (FirstOrder.lean:1201). Specialised to
`params = []`. -/
theorem collectCalls_preserves_AppRefToDt {tds : Typed.Decls}
    {term : Typed.Term} (hAR : Typed.Term.AppRefToDt tds [] term) :
    ∀ (seen : Std.HashSet (Global × Array Typ)),
      (∀ entry ∈ seen, ∀ t ∈ entry.2, Typed.Typ.AppRefToDt tds [] t) →
      ∀ entry ∈ collectCalls tds seen term, ∀ t ∈ entry.2,
        Typed.Typ.AppRefToDt tds [] t := by
  induction hAR with
  | unit _ => intro seen hseen; unfold collectCalls; exact hseen
  | var _ => intro seen hseen; unfold collectCalls; exact hseen
  | @ref typ e g tArgs _htyp hArgs =>
    intro seen hseen
    show ∀ entry ∈ collectCalls tds seen (.ref typ e g tArgs), _
    unfold collectCalls
    by_cases htA : tArgs.isEmpty = true
    · rw [if_pos htA]; exact hseen
    · rw [if_neg htA]
      cases hg : tds.getByKey g with
      | none => exact hseen
      | some d =>
        cases d with
        | function f =>
          intro entry hent t ht
          rcases Std.HashSet.mem_insert.mp hent with hbeq | hin
          · have hpair : (g, tArgs) = entry := LawfulBEq.eq_of_beq hbeq
            rw [← hpair] at ht; exact hArgs t ht
          · exact hseen entry hin t ht
        | dataType _ => exact hseen
        | constructor dt _ =>
          intro entry hent t ht
          rcases Std.HashSet.mem_insert.mp hent with hbeq | hin
          · have hpair : (dt.name, tArgs) = entry := LawfulBEq.eq_of_beq hbeq
            rw [← hpair] at ht; exact hArgs t ht
          · exact hseen entry hin t ht
  | field _ => intro seen hseen; unfold collectCalls; exact hseen
  | @tuple typ e ts _htyp _h ih =>
    intro seen hseen
    unfold collectCalls
    apply Array.foldl_induction
      (motive := fun (_ : Nat) (acc : Std.HashSet (Global × Array Typ)) =>
        ∀ entry ∈ acc, ∀ t ∈ entry.2, Typed.Typ.AppRefToDt tds [] t) hseen
    intro i acc hinv
    obtain ⟨t, ht⟩ := ts.attach[i.val]'i.isLt
    exact ih t ht acc hinv
  | @array typ e ts _htyp _h ih =>
    intro seen hseen
    unfold collectCalls
    apply Array.foldl_induction
      (motive := fun (_ : Nat) (acc : Std.HashSet (Global × Array Typ)) =>
        ∀ entry ∈ acc, ∀ t ∈ entry.2, Typed.Typ.AppRefToDt tds [] t) hseen
    intro i acc hinv
    obtain ⟨t, ht⟩ := ts.attach[i.val]'i.isLt
    exact ih t ht acc hinv
  | @ret typ e sub _htyp _h ih => intro seen hseen; unfold collectCalls; exact ih _ hseen
  | @«let» typ e pat v b _htyp _hv _hb ihv ihb =>
    intro seen hseen; unfold collectCalls; exact ihb _ (ihv _ hseen)
  | @«match» typ e scrut cases _htyp _hscrut _hcases ihscrut ih_cases =>
    intro seen hseen
    unfold collectCalls
    have h_scrut := ihscrut _ hseen
    have aux : ∀ (l : List {x // x ∈ cases})
        (acc : Std.HashSet (Global × Array Typ)),
        (∀ entry ∈ acc, ∀ t' ∈ entry.2, Typed.Typ.AppRefToDt tds [] t') →
        ∀ entry ∈ l.foldl
          (fun s x => match x with | ⟨(_, b), _⟩ => collectCalls tds s b) acc,
          ∀ t' ∈ entry.2, Typed.Typ.AppRefToDt tds [] t' := by
      intro l
      induction l with
      | nil => intro acc hacc entry hent; exact hacc entry hent
      | cons hd tl ih_l =>
        intro acc hacc
        simp only [List.foldl_cons]
        apply ih_l
        obtain ⟨pc, hpc⟩ := hd
        obtain ⟨pat, b⟩ := pc
        exact ih_cases ⟨pat, b⟩ hpc acc hacc
    exact aux cases.attach _ h_scrut
  | @app typ e g tArgs args u _htyp hArgs _hargs ihargs =>
    intro seen hseen
    unfold collectCalls
    have h_after_args : ∀ entry ∈ args.attach.foldl
        (fun s ⟨a, _⟩ => collectCalls tds s a) seen,
        ∀ t' ∈ entry.2, Typed.Typ.AppRefToDt tds [] t' := by
      have aux : ∀ (l : List {x // x ∈ args})
          (acc : Std.HashSet (Global × Array Typ)),
          (∀ entry ∈ acc, ∀ t' ∈ entry.2, Typed.Typ.AppRefToDt tds [] t') →
          ∀ entry ∈ l.foldl (fun s ⟨a, _⟩ => collectCalls tds s a) acc,
            ∀ t' ∈ entry.2, Typed.Typ.AppRefToDt tds [] t' := by
        intro l
        induction l with
        | nil => intro acc hacc entry hent; exact hacc entry hent
        | cons hd tl ih_l =>
          intro acc hacc
          simp only [List.foldl_cons]
          apply ih_l
          obtain ⟨a, ha⟩ := hd
          exact ihargs a ha acc hacc
      exact aux args.attach _ hseen
    by_cases htA : tArgs.isEmpty = true
    · rw [if_pos htA]; exact h_after_args
    · rw [if_neg htA]
      cases hg : tds.getByKey g with
      | none => exact h_after_args
      | some d =>
        cases d with
        | function f =>
          intro entry hent t ht
          rcases Std.HashSet.mem_insert.mp hent with hbeq | hin
          · have hpair : (g, tArgs) = entry := LawfulBEq.eq_of_beq hbeq
            rw [← hpair] at ht; exact hArgs t ht
          · exact h_after_args entry hin t ht
        | dataType _ => exact h_after_args
        | constructor dt _ =>
          intro entry hent t ht
          rcases Std.HashSet.mem_insert.mp hent with hbeq | hin
          · have hpair : (dt.name, tArgs) = entry := LawfulBEq.eq_of_beq hbeq
            rw [← hpair] at ht; exact hArgs t ht
          · exact h_after_args entry hin t ht
  | @add typ e a b _htyp _ha _hb iha ihb | @sub typ e a b _htyp _ha _hb iha ihb
  | @mul typ e a b _htyp _ha _hb iha ihb | @u8Xor typ e a b _htyp _ha _hb iha ihb
  | @u8Add typ e a b _htyp _ha _hb iha ihb | @u8Sub typ e a b _htyp _ha _hb iha ihb
  | @u8And typ e a b _htyp _ha _hb iha ihb | @u8Or typ e a b _htyp _ha _hb iha ihb
  | @u8LessThan typ e a b _htyp _ha _hb iha ihb
  | @u32LessThan typ e a b _htyp _ha _hb iha ihb =>
    intro seen hseen; unfold collectCalls; exact ihb _ (iha _ hseen)
  | @eqZero typ e a _htyp _ha iha | @store typ e a _htyp _ha iha
  | @load typ e a _htyp _ha iha | @ptrVal typ e a _htyp _ha iha
  | @u8BitDecomposition typ e a _htyp _ha iha
  | @u8ShiftLeft typ e a _htyp _ha iha | @u8ShiftRight typ e a _htyp _ha iha
  | @ioGetInfo typ e a _htyp _ha iha =>
    intro seen hseen; unfold collectCalls; exact iha _ hseen
  | @proj typ e a n _htyp _ha iha | @get typ e a n _htyp _ha iha =>
    intro seen hseen; unfold collectCalls; exact iha _ hseen
  | @slice typ e a i j _htyp _ha iha =>
    intro seen hseen; unfold collectCalls; exact iha _ hseen
  | @«set» typ e a n v _htyp _ha _hv iha ihv =>
    intro seen hseen; unfold collectCalls; exact ihv _ (iha _ hseen)
  | @assertEq typ e a b r _htyp _ha _hb _hr iha ihb ihr =>
    intro seen hseen; unfold collectCalls; exact ihr _ (ihb _ (iha _ hseen))
  | @ioSetInfo typ e k i l r _htyp _hk _hi _hl _hr ihk ihi ihl ihr =>
    intro seen hseen; unfold collectCalls; exact ihr _ (ihl _ (ihi _ (ihk _ hseen)))
  | @ioRead typ e i n _htyp _hi ihi =>
    intro seen hseen; unfold collectCalls; exact ihi _ hseen
  | @ioWrite typ e d r _htyp _hd _hr ihd ihr =>
    intro seen hseen; unfold collectCalls; exact ihr _ (ihd _ hseen)
  | @debug typ e label t r _htyp _ht _hr iht ihr =>
    intro seen hseen
    unfold collectCalls
    have h_t : ∀ entry ∈ (match t with
                          | some t => collectCalls tds seen t
                          | none => seen),
        ∀ t' ∈ entry.2, Typed.Typ.AppRefToDt tds [] t' := by
      cases t with
      | none => exact hseen
      | some tval => exact iht tval rfl _ hseen
    exact ihr _ h_t

/-- `substInTypedTerm` lifts `Typed.Term.AppRefToDt tds P_in body` to
`Typed.Term.AppRefToDt tds P_out (substInTypedTerm subst body)` given subst
maps every name to a `P_out`-AppRefToDt-safe type and is total on `P_in`'s
type-parameter names. Mirrors `substInTypedTerm_preserves_AppRefTArgsFO`
(FirstOrder.lean:1446) with `AppRefToDt` instead of `AppRefTArgsFO`. -/
theorem substInTypedTerm_preserves_AppRefToDt
    {tds : Typed.Decls} {P_in P_out : List String}
    {body : Typed.Term} {subst : Global → Option Typ}
    (hsubst : ∀ g t', subst g = some t' → Typed.Typ.AppRefToDt tds P_out t')
    (hsubst_total : ∀ g, (∃ p ∈ P_in, g = Global.init p) →
      ∃ t', subst g = some t')
    (hbody : Typed.Term.AppRefToDt tds P_in body) :
    Typed.Term.AppRefToDt tds P_out (substInTypedTerm subst body) := by
  induction hbody with
  | unit htyp =>
    unfold substInTypedTerm
    exact .unit (Typ.instantiate_preserves_AppRefToDt subst hsubst hsubst_total htyp)
  | var htyp =>
    unfold substInTypedTerm
    exact .var (Typ.instantiate_preserves_AppRefToDt subst hsubst hsubst_total htyp)
  | @ref typ e g tArgs htyp hArgs =>
    unfold substInTypedTerm
    refine .ref
      (Typ.instantiate_preserves_AppRefToDt subst hsubst hsubst_total htyp) ?_
    intro t' ht'
    rw [Array.mem_map] at ht'
    obtain ⟨t0, ht0mem, ht0eq⟩ := ht'
    subst ht0eq
    exact Typ.instantiate_preserves_AppRefToDt subst hsubst hsubst_total
      (hArgs t0 ht0mem)
  | field htyp =>
    unfold substInTypedTerm
    exact .field (Typ.instantiate_preserves_AppRefToDt subst hsubst hsubst_total htyp)
  | @tuple typ e ts htyp _h ih =>
    unfold substInTypedTerm
    refine .tuple
      (Typ.instantiate_preserves_AppRefToDt subst hsubst hsubst_total htyp) ?_
    intro sub hsub
    obtain ⟨t0, ht0mem, ht0eq⟩ := mem_of_attach_map ts _ hsub
    subst ht0eq
    exact ih t0 ht0mem
  | @array typ e ts htyp _h ih =>
    unfold substInTypedTerm
    refine .array
      (Typ.instantiate_preserves_AppRefToDt subst hsubst hsubst_total htyp) ?_
    intro sub hsub
    obtain ⟨t0, ht0mem, ht0eq⟩ := mem_of_attach_map ts _ hsub
    subst ht0eq
    exact ih t0 ht0mem
  | @ret typ e r htyp _h ih =>
    unfold substInTypedTerm
    exact .ret (Typ.instantiate_preserves_AppRefToDt subst hsubst hsubst_total htyp) ih
  | @«let» typ e p v b htyp _hv _hb ihv ihb =>
    unfold substInTypedTerm
    exact .let
      (Typ.instantiate_preserves_AppRefToDt subst hsubst hsubst_total htyp) ihv ihb
  | @«match» typ e scrut cases htyp _hscrut _hcases ihscrut ihcases =>
    unfold substInTypedTerm
    refine .match
      (Typ.instantiate_preserves_AppRefToDt subst hsubst hsubst_total htyp)
      ihscrut ?_
    intro pc hpc
    obtain ⟨p0, hp0mem, hp0eq⟩ := list_mem_of_attach_map cases _ hpc
    subst hp0eq
    exact ihcases p0 hp0mem
  | @app typ e g tArgs args u htyp hArgs _hargs ihargs =>
    unfold substInTypedTerm
    refine .app
      (Typ.instantiate_preserves_AppRefToDt subst hsubst hsubst_total htyp) ?_ ?_
    · intro t' ht'
      rw [Array.mem_map] at ht'
      obtain ⟨t0, ht0mem, ht0eq⟩ := ht'
      subst ht0eq
      exact Typ.instantiate_preserves_AppRefToDt subst hsubst hsubst_total
        (hArgs t0 ht0mem)
    · intro a ha
      obtain ⟨a0, ha0mem, ha0eq⟩ := list_mem_of_attach_map args _ ha
      subst ha0eq
      exact ihargs a0 ha0mem
  | add htyp _ _ iha ihb =>
    unfold substInTypedTerm
    exact .add (Typ.instantiate_preserves_AppRefToDt subst hsubst hsubst_total htyp) iha ihb
  | sub htyp _ _ iha ihb =>
    unfold substInTypedTerm
    exact .sub (Typ.instantiate_preserves_AppRefToDt subst hsubst hsubst_total htyp) iha ihb
  | mul htyp _ _ iha ihb =>
    unfold substInTypedTerm
    exact .mul (Typ.instantiate_preserves_AppRefToDt subst hsubst hsubst_total htyp) iha ihb
  | eqZero htyp _ iha =>
    unfold substInTypedTerm
    exact .eqZero (Typ.instantiate_preserves_AppRefToDt subst hsubst hsubst_total htyp) iha
  | proj htyp _ iha =>
    unfold substInTypedTerm
    exact .proj (Typ.instantiate_preserves_AppRefToDt subst hsubst hsubst_total htyp) iha
  | get htyp _ iha =>
    unfold substInTypedTerm
    exact .get (Typ.instantiate_preserves_AppRefToDt subst hsubst hsubst_total htyp) iha
  | slice htyp _ iha =>
    unfold substInTypedTerm
    exact .slice (Typ.instantiate_preserves_AppRefToDt subst hsubst hsubst_total htyp) iha
  | «set» htyp _ _ iha ihv =>
    unfold substInTypedTerm
    exact .set (Typ.instantiate_preserves_AppRefToDt subst hsubst hsubst_total htyp) iha ihv
  | store htyp _ iha =>
    unfold substInTypedTerm
    exact .store (Typ.instantiate_preserves_AppRefToDt subst hsubst hsubst_total htyp) iha
  | load htyp _ iha =>
    unfold substInTypedTerm
    exact .load (Typ.instantiate_preserves_AppRefToDt subst hsubst hsubst_total htyp) iha
  | ptrVal htyp _ iha =>
    unfold substInTypedTerm
    exact .ptrVal (Typ.instantiate_preserves_AppRefToDt subst hsubst hsubst_total htyp) iha
  | assertEq htyp _ _ _ iha ihb ihr =>
    unfold substInTypedTerm
    exact .assertEq
      (Typ.instantiate_preserves_AppRefToDt subst hsubst hsubst_total htyp) iha ihb ihr
  | ioGetInfo htyp _ ihk =>
    unfold substInTypedTerm
    exact .ioGetInfo
      (Typ.instantiate_preserves_AppRefToDt subst hsubst hsubst_total htyp) ihk
  | ioSetInfo htyp _ _ _ _ ihk ihi ihl ihr =>
    unfold substInTypedTerm
    exact .ioSetInfo
      (Typ.instantiate_preserves_AppRefToDt subst hsubst hsubst_total htyp) ihk ihi ihl ihr
  | ioRead htyp _ ihi =>
    unfold substInTypedTerm
    exact .ioRead
      (Typ.instantiate_preserves_AppRefToDt subst hsubst hsubst_total htyp) ihi
  | ioWrite htyp _ _ ihd ihr =>
    unfold substInTypedTerm
    exact .ioWrite
      (Typ.instantiate_preserves_AppRefToDt subst hsubst hsubst_total htyp) ihd ihr
  | u8BitDecomposition htyp _ iha =>
    unfold substInTypedTerm
    exact .u8BitDecomposition
      (Typ.instantiate_preserves_AppRefToDt subst hsubst hsubst_total htyp) iha
  | u8ShiftLeft htyp _ iha =>
    unfold substInTypedTerm
    exact .u8ShiftLeft
      (Typ.instantiate_preserves_AppRefToDt subst hsubst hsubst_total htyp) iha
  | u8ShiftRight htyp _ iha =>
    unfold substInTypedTerm
    exact .u8ShiftRight
      (Typ.instantiate_preserves_AppRefToDt subst hsubst hsubst_total htyp) iha
  | u8Xor htyp _ _ iha ihb =>
    unfold substInTypedTerm
    exact .u8Xor (Typ.instantiate_preserves_AppRefToDt subst hsubst hsubst_total htyp) iha ihb
  | u8Add htyp _ _ iha ihb =>
    unfold substInTypedTerm
    exact .u8Add (Typ.instantiate_preserves_AppRefToDt subst hsubst hsubst_total htyp) iha ihb
  | u8Sub htyp _ _ iha ihb =>
    unfold substInTypedTerm
    exact .u8Sub (Typ.instantiate_preserves_AppRefToDt subst hsubst hsubst_total htyp) iha ihb
  | u8And htyp _ _ iha ihb =>
    unfold substInTypedTerm
    exact .u8And (Typ.instantiate_preserves_AppRefToDt subst hsubst hsubst_total htyp) iha ihb
  | u8Or htyp _ _ iha ihb =>
    unfold substInTypedTerm
    exact .u8Or (Typ.instantiate_preserves_AppRefToDt subst hsubst hsubst_total htyp) iha ihb
  | u8LessThan htyp _ _ iha ihb =>
    unfold substInTypedTerm
    exact .u8LessThan
      (Typ.instantiate_preserves_AppRefToDt subst hsubst hsubst_total htyp) iha ihb
  | u32LessThan htyp _ _ iha ihb =>
    unfold substInTypedTerm
    exact .u32LessThan
      (Typ.instantiate_preserves_AppRefToDt subst hsubst hsubst_total htyp) iha ihb
  | @debug typ e label t r htyp ht _hr iht ihr =>
    unfold substInTypedTerm
    refine .debug
      (Typ.instantiate_preserves_AppRefToDt subst hsubst hsubst_total htyp) ?_ ihr
    intro tval htval
    cases t with
    | none => cases htval
    | some sub =>
      simp only [Option.some.injEq] at htval
      subst htval
      exact iht sub rfl

/-! #### `CtorArgsAppRefToDt` drain chain (4 levels). -/

/-- Init clause: at the seed state, `newDataTypes = #[]` so the invariant
holds vacuously. -/
theorem DrainState.CtorArgsAppRefToDt.init
    (tds : Typed.Decls) (pending : Std.HashSet (Global × Array Typ)) :
    DrainState.CtorArgsAppRefToDt tds
      { pending, seen := {}, mono := {},
        newFunctions := #[], newDataTypes := #[] } := by
  intro dt hdt
  simp only [Array.not_mem_empty] at hdt

/-- Init clause for `PendingArgsAppRefToDt`: under
`Typed.Decls.AllAppRefToDt tds`, the seed's pending entries have
AppRefToDt-safe args.

Sig amendment 2026-05-03 (Invariant 3, Defect 3): `_hCtor` premise
broadened from the narrow `AllCtorArgsAppRefToDt` to the bundled
`AllAppRefToDt` (which adds `AllFnInputsAppRefToDt +
AllFnOutputAppRefToDt + AllFnBodyAppRefToDt`). The narrow form was
provably insufficient — the seed traverses function bodies/inputs/outputs
via `collectInTypedTerm`/`collectInTyp`, so pending entries can carry
`tArgs` sourced from any of those positions, not just ctor argTypes.

BLOCKED-AppRefToDt-seed-init body: the seed iterates over both
`.function f` and `.dataType dt` decls, calling `collectInTyp`/
`collectInTypedTerm`/`collectCalls` on bodies, inputs, outputs, and
ctor argTypes. Closure path:
mirror `concretizeSeed_PendingArgsFO` (FirstOrder.lean:1628) using the
new (NEW NEW) helpers `collectInTyp_preserves_AppRefToDt`,
`collectInTypedTerm_preserves_AppRefToDt`,
`collectCalls_preserves_AppRefToDt`. Each helper is a structural
recursion mirroring its FO analog. Body deferred — the sig is now sound,
the body work is mechanical translation.  -/
theorem DrainState.PendingArgsAppRefToDt.init
    {tds : Typed.Decls}
    (hAll : Typed.Decls.AllAppRefToDt tds) :
    DrainState.PendingArgsAppRefToDt tds
      { pending := concretizeSeed tds, seen := {}, mono := {},
        newFunctions := #[], newDataTypes := #[] } := by
  -- Mirror of `concretizeSeed_PendingArgsFO` (FirstOrder.lean:1628).
  obtain ⟨hCtor, hFnIn, hFnOut, hFnBody⟩ := hAll
  unfold concretizeSeed
  show ∀ entry ∈ _, _
  apply Array.foldl_induction
    (motive := fun (_ : Nat) (acc : Std.HashSet (Global × Array Typ)) =>
      ∀ entry ∈ acc, ∀ t ∈ entry.2, Typed.Typ.AppRefToDt tds [] t)
  · intro entry hent
    -- empty HashSet: no entries.
    simp at hent
  · intro i acc hinv
    let p := tds.pairs[i.val]'i.isLt
    have hpmem : p ∈ tds.pairs.toList :=
      Array.mem_toList_iff.mpr (Array.getElem_mem _)
    have hp_get : tds.getByKey p.1 = some p.2 :=
      IndexMap.getByKey_of_mem_pairs _ _ _ hpmem
    cases hd : p.snd with
    | function f =>
      simp only [hd]
      by_cases hp : f.params.isEmpty = true
      · rw [if_pos hp]
        have hp_list : f.params = [] := List.isEmpty_iff.mp hp
        have hf_get : tds.getByKey p.1 = some (.function f) := by rw [← hd]; exact hp_get
        -- Pull per-position witnesses; rewrite f.params to [].
        have h_inputs := hFnIn p.1 f hf_get
        have h_output := hFnOut p.1 f hf_get
        have h_body := hFnBody p.1 f hf_get
        rw [hp_list] at h_inputs h_output h_body
        -- After collectInTyp acc f.output.
        have h1 : ∀ entry ∈ collectInTyp acc f.output, ∀ t ∈ entry.2,
            Typed.Typ.AppRefToDt tds [] t :=
          collectInTyp_preserves_AppRefToDt h_output acc hinv
        -- After f.inputs.foldl.
        have h2 : ∀ entry ∈ f.inputs.foldl (fun s (_, t) => collectInTyp s t)
            (collectInTyp acc f.output), ∀ t ∈ entry.2,
            Typed.Typ.AppRefToDt tds [] t := by
          have aux : ∀ (l : List (Local × Typ))
              (acc' : Std.HashSet (Global × Array Typ)),
              (∀ entry ∈ acc', ∀ t ∈ entry.2, Typed.Typ.AppRefToDt tds [] t) →
              (∀ p ∈ l, Typed.Typ.AppRefToDt tds [] p.2) →
              ∀ entry ∈ l.foldl (fun s (_, t) => collectInTyp s t) acc',
                ∀ t ∈ entry.2, Typed.Typ.AppRefToDt tds [] t := by
            intro l
            induction l with
            | nil => intro acc' hacc' _ entry hent; exact hacc' entry hent
            | cons hd' tl ih_l =>
              intro acc' hacc' hcs
              simp only [List.foldl_cons]
              apply ih_l
              · obtain ⟨_, t⟩ := hd'
                exact collectInTyp_preserves_AppRefToDt
                  (hcs (_, t) List.mem_cons_self) acc' hacc'
              · intro p' hp'; exact hcs p' (List.mem_cons_of_mem _ hp')
          apply aux f.inputs _ h1
          intro p' hp'
          exact h_inputs p' hp'
        -- After collectInTypedTerm body.
        have h3 := collectInTypedTerm_preserves_AppRefToDt h_body _ h2
        -- After collectCalls body.
        exact collectCalls_preserves_AppRefToDt h_body _ h3
      · rw [if_neg hp]; exact hinv
    | dataType dt =>
      simp only [hd]
      by_cases hp : dt.params.isEmpty = true
      · rw [if_pos hp]
        have hp_list : dt.params = [] := List.isEmpty_iff.mp hp
        have hd_get : tds.getByKey p.1 = some (.dataType dt) := by rw [← hd]; exact hp_get
        have h_dt : ∀ c ∈ dt.constructors, ∀ t ∈ c.argTypes,
            Typed.Typ.AppRefToDt tds [] t := by
          intro c hc t ht
          have h := hCtor p.1 dt c hd_get hc t ht
          rw [hp_list] at h
          exact h
        have aux_inner : ∀ (l : List Typ)
            (acc' : Std.HashSet (Global × Array Typ)),
            (∀ entry ∈ acc', ∀ t ∈ entry.2, Typed.Typ.AppRefToDt tds [] t) →
            (∀ t ∈ l, Typed.Typ.AppRefToDt tds [] t) →
            ∀ entry ∈ l.foldl collectInTyp acc',
              ∀ t ∈ entry.2, Typed.Typ.AppRefToDt tds [] t := by
          intro l
          induction l with
          | nil => intro acc' hacc' _ entry hent; exact hacc' entry hent
          | cons hd' tl ih_l =>
            intro acc' hacc' hcs
            simp only [List.foldl_cons]
            apply ih_l
            · exact collectInTyp_preserves_AppRefToDt
                (hcs hd' List.mem_cons_self) acc' hacc'
            · intro t' ht'; exact hcs t' (List.mem_cons_of_mem _ ht')
        have aux : ∀ (cs : List Constructor)
            (acc' : Std.HashSet (Global × Array Typ)),
            (∀ entry ∈ acc', ∀ t ∈ entry.2, Typed.Typ.AppRefToDt tds [] t) →
            (∀ c ∈ cs, ∀ t ∈ c.argTypes, Typed.Typ.AppRefToDt tds [] t) →
            ∀ entry ∈ cs.foldl (fun s c => c.argTypes.foldl collectInTyp s) acc',
              ∀ t ∈ entry.2, Typed.Typ.AppRefToDt tds [] t := by
          intro cs
          induction cs with
          | nil => intro acc' hacc' _ entry hent; exact hacc' entry hent
          | cons hd' tl ih_l =>
            intro acc' hacc' hcs
            simp only [List.foldl_cons]
            apply ih_l
            · exact aux_inner hd'.argTypes acc' hacc'
                (fun t ht => hcs hd' List.mem_cons_self t ht)
            · intro c hc; exact hcs c (List.mem_cons_of_mem _ hc)
        exact aux dt.constructors _ hinv h_dt
      · rw [if_neg hp]; exact hinv
    | constructor _ _ =>
      simp only [hd]; exact hinv

/-- Drain entry preservation for `CtorArgsAppRefToDt`. Three arms:
* `.function`: doesn't touch `newDataTypes`, trivially preserves.
* `.dataType`: pushes a new dt with `newCtors`. Each new ctor argType
  = `Typ.instantiate subst t` where `t` is from the original dt's ctor
  argTypes (AppRefToDt by `AllCtorArgsAppRefToDt tds` precondition) and
  `subst = mkParamSubst dt.params entry.2` (subst image is in `entry.2`,
  AppRefToDt by `PendingArgsAppRefToDt` precondition). Apply
  `Typ.instantiate_preserves_AppRefToDt`.
* Throw arm: contradicts `hstep` success. -/
theorem concretizeDrainEntry_preserves_CtorArgsAppRefToDt
    {tds : Typed.Decls}
    (hCtor : Typed.Decls.AllCtorArgsAppRefToDt tds)
    {state state' : DrainState}
    (hinv : state.CtorArgsAppRefToDt tds)
    (entry : Global × Array Typ)
    (hpargs : ∀ t ∈ entry.2, Typed.Typ.AppRefToDt tds [] t)
    (hstep : concretizeDrainEntry tds state entry = .ok state') :
    state'.CtorArgsAppRefToDt tds := by
  unfold concretizeDrainEntry at hstep
  simp only [bind, Except.bind, pure, Except.pure] at hstep
  by_cases hseen : state.seen.contains (entry.1, entry.2)
  · simp [hseen] at hstep
    rw [← hstep]; exact hinv
  · simp [hseen] at hstep
    split at hstep
    · -- function arm — newDataTypes unchanged.
      rename_i f hf_get
      split at hstep
      · simp only [Except.ok.injEq] at hstep
        rw [← hstep]
        intro dt hdt c hc t ht
        exact hinv dt hdt c hc t ht
      · exact absurd hstep (by intro h; cases h)
    · -- dataType arm — pushes a new dt.
      rename_i dt hdt_get
      split at hstep
      · simp only [Except.ok.injEq] at hstep
        rw [← hstep]
        let subst := mkParamSubst dt.params entry.2
        have hsubst_AR : ∀ g t', subst g = some t' →
            Typed.Typ.AppRefToDt tds [] t' :=
          fun g t' h => hpargs t' (mkParamSubst_some_mem _ _ h)
        -- Subst is total on dt.params via `mkParamSubst_total_on_params`.
        -- Requires arity `entry.2.size = dt.params.length` from the
        -- precondition guarding the success of the dataType arm of
        -- `concretizeDrainEntry`.
        have hsubst_total : ∀ g, (∃ p ∈ dt.params, g = Global.init p) →
            ∃ t', subst g = some t' := by
          intro g hin
          have h_arity : entry.2.size = dt.params.length := by
            -- Extracted from the success-guard of `concretizeDrainEntry`'s
            -- dataType arm. The arm only succeeds when the arity check passes.
            rename_i hsize_eq
            have h := (by simpa [beq_iff_eq] using hsize_eq : dt.params.length = entry.2.size)
            exact h.symm
          exact mkParamSubst_total_on_params dt.params entry.2 h_arity hin
        intro dt' hdt'_mem c' hc' t' ht'
        rcases Array.mem_push.mp hdt'_mem with hin | heq
        · exact hinv dt' hin c' hc' t' ht'
        · -- dt' = newDt where newCtors are dt.constructors with substituted argTypes.
          subst heq
          -- c' ∈ newCtors = dt.constructors.map (...).
          simp only at hc'
          rw [List.mem_map] at hc'
          obtain ⟨c0, hc0_mem, hc0_eq⟩ := hc'
          subst hc0_eq
          -- t' ∈ c0.argTypes.map (Typ.instantiate subst).
          simp only at ht'
          rw [List.mem_map] at ht'
          obtain ⟨t0, ht0_mem, ht0_eq⟩ := ht'
          subst ht0_eq
          -- Original t0 is AppRefToDt under dt.params via AllCtorArgsAppRefToDt;
          -- instantiate substitutes those params away → AppRefToDt under [].
          have h_t0_AR : Typed.Typ.AppRefToDt tds dt.params t0 :=
            hCtor entry.1 dt c0 hdt_get hc0_mem t0 ht0_mem
          exact Typ.instantiate_preserves_AppRefToDt subst hsubst_AR hsubst_total h_t0_AR
      · exact absurd hstep (by intro h; cases h)
    · cases hstep

/-- Drain entry preservation for `PendingArgsAppRefToDt`. Mirrors
`concretizeDrainEntry_preserves_PendingArgsFO` (FirstOrder.lean:2021) using
`AppRefToDt` instead of `FirstOrder`/`AppRefTArgsFO`. Sig amendment
2026-05-04: hypothesis broadened from the narrow `AllCtorArgsAppRefToDt`
to the bundled `AllAppRefToDt` — the function arm needs body/inputs/output
witnesses, not just ctor argTypes. -/
theorem concretizeDrainEntry_preserves_PendingArgsAppRefToDt
    {tds : Typed.Decls}
    (hAll : Typed.Decls.AllAppRefToDt tds)
    {state state' : DrainState}
    (hinv : state.PendingArgsAppRefToDt tds)
    (entry : Global × Array Typ)
    (hpargs : ∀ t ∈ entry.2, Typed.Typ.AppRefToDt tds [] t)
    (hstep : concretizeDrainEntry tds state entry = .ok state') :
    state'.PendingArgsAppRefToDt tds := by
  obtain ⟨hCtor, hFnIn, hFnOut, hFnBody⟩ := hAll
  unfold concretizeDrainEntry at hstep
  simp only [bind, Except.bind, pure, Except.pure] at hstep
  by_cases hseen : state.seen.contains (entry.1, entry.2)
  · simp [hseen] at hstep
    rw [← hstep]; exact hinv
  · simp [hseen] at hstep
    have hinv_pending : ∀ p ∈ state.pending, ∀ t ∈ p.2,
        Typed.Typ.AppRefToDt tds [] t := hinv
    split at hstep
    · -- function arm.
      rename_i f hf_get
      split at hstep
      · simp only [Except.ok.injEq] at hstep
        rw [← hstep]
        let subst := mkParamSubst f.params entry.2
        have hsubst_AR : ∀ g t', subst g = some t' →
            Typed.Typ.AppRefToDt tds [] t' :=
          fun g t' h => hpargs t' (mkParamSubst_some_mem _ _ h)
        have hsubst_total : ∀ g, (∃ p ∈ f.params, g = Global.init p) →
            ∃ t', subst g = some t' := by
          intro g hin
          have h_arity : entry.2.size = f.params.length := by
            rename_i hsize_eq
            have h := (by simpa [beq_iff_eq] using hsize_eq :
              f.params.length = entry.2.size)
            exact h.symm
          exact mkParamSubst_total_on_params f.params entry.2 h_arity hin
        -- Source template positions are AppRefToDt-safe under f.params.
        have h_inputs := hFnIn entry.1 f hf_get
        have h_output := hFnOut entry.1 f hf_get
        have h_body := hFnBody entry.1 f hf_get
        -- After-instantiate witnesses (params=[]).
        have h_newOutput :
            Typed.Typ.AppRefToDt tds [] (Typ.instantiate subst f.output) :=
          Typ.instantiate_preserves_AppRefToDt subst hsubst_AR hsubst_total h_output
        have h_newInputs : ∀ p ∈ f.inputs.map
            (fun (l, t) => (l, Typ.instantiate subst t)),
            Typed.Typ.AppRefToDt tds [] p.2 := by
          intro p hp
          rw [List.mem_map] at hp
          obtain ⟨⟨l, t⟩, ht_mem, ht_eq⟩ := hp
          subst ht_eq
          exact Typ.instantiate_preserves_AppRefToDt subst hsubst_AR hsubst_total
            (h_inputs (l, t) ht_mem)
        have h_newBody :
            Typed.Term.AppRefToDt tds [] (substInTypedTerm subst f.body) :=
          substInTypedTerm_preserves_AppRefToDt hsubst_AR hsubst_total h_body
        -- Now chain L4a (output) → L4a per input → L4b → L4c.
        intro p hp
        have h1 : ∀ p' ∈ collectInTyp state.pending
            (Typ.instantiate subst f.output),
            ∀ t ∈ p'.2, Typed.Typ.AppRefToDt tds [] t :=
          collectInTyp_preserves_AppRefToDt h_newOutput _ hinv_pending
        have h2 : ∀ p' ∈ (f.inputs.map
            (fun (l, t) => (l, Typ.instantiate subst t))).foldl
            (fun s (_, t) => collectInTyp s t)
            (collectInTyp state.pending (Typ.instantiate subst f.output)),
            ∀ t ∈ p'.2, Typed.Typ.AppRefToDt tds [] t := by
          have aux : ∀ (l : List (Local × Typ))
              (acc : Std.HashSet (Global × Array Typ)),
              (∀ p' ∈ acc, ∀ t ∈ p'.2, Typed.Typ.AppRefToDt tds [] t) →
              (∀ p' ∈ l, Typed.Typ.AppRefToDt tds [] p'.2) →
              ∀ p' ∈ l.foldl (fun s (_, t) => collectInTyp s t) acc,
                ∀ t ∈ p'.2, Typed.Typ.AppRefToDt tds [] t := by
            intro l
            induction l with
            | nil => intro acc hacc _ p' hp'; exact hacc p' hp'
            | cons hd tl ih_l =>
              intro acc hacc hcs
              simp only [List.foldl_cons]
              apply ih_l
              · obtain ⟨_, t⟩ := hd
                exact collectInTyp_preserves_AppRefToDt
                  (hcs (_, t) List.mem_cons_self) acc hacc
              · intro p' hp'; exact hcs p' (List.mem_cons_of_mem _ hp')
          exact aux _ _ h1 h_newInputs
        have h3 := collectInTypedTerm_preserves_AppRefToDt h_newBody _ h2
        have h4 := collectCalls_preserves_AppRefToDt (tds := tds) h_newBody _ h3
        exact h4 p hp
      · exact absurd hstep (by intro h; cases h)
    · -- dataType arm.
      rename_i dt hdt_get
      split at hstep
      · simp only [Except.ok.injEq] at hstep
        rw [← hstep]
        let subst := mkParamSubst dt.params entry.2
        have hsubst_AR : ∀ g t', subst g = some t' →
            Typed.Typ.AppRefToDt tds [] t' :=
          fun g t' h => hpargs t' (mkParamSubst_some_mem _ _ h)
        have hsubst_total : ∀ g, (∃ p ∈ dt.params, g = Global.init p) →
            ∃ t', subst g = some t' := by
          intro g hin
          have h_arity : entry.2.size = dt.params.length := by
            rename_i hsize_eq
            have h := (by simpa [beq_iff_eq] using hsize_eq :
              dt.params.length = entry.2.size)
            exact h.symm
          exact mkParamSubst_total_on_params dt.params entry.2 h_arity hin
        have h_dt : ∀ c ∈ dt.constructors, ∀ t ∈ c.argTypes,
            Typed.Typ.AppRefToDt tds dt.params t :=
          fun c hc t ht => hCtor entry.1 dt c hdt_get hc t ht
        intro p hp
        have aux_inner : ∀ (l : List Typ)
            (acc : Std.HashSet (Global × Array Typ)),
            (∀ p' ∈ acc, ∀ t ∈ p'.2, Typed.Typ.AppRefToDt tds [] t) →
            (∀ t ∈ l, Typed.Typ.AppRefToDt tds [] t) →
            ∀ p' ∈ l.foldl collectInTyp acc,
              ∀ t ∈ p'.2, Typed.Typ.AppRefToDt tds [] t := by
          intro l
          induction l with
          | nil => intro acc hacc _ p' hp'; exact hacc p' hp'
          | cons hd tl ih_l =>
            intro acc hacc hcs
            simp only [List.foldl_cons]
            apply ih_l
            · exact collectInTyp_preserves_AppRefToDt
                (hcs hd List.mem_cons_self) acc hacc
            · intro t' ht'; exact hcs t' (List.mem_cons_of_mem _ ht')
        have aux : ∀ (cs : List Constructor)
            (acc : Std.HashSet (Global × Array Typ)),
            (∀ p' ∈ acc, ∀ t ∈ p'.2, Typed.Typ.AppRefToDt tds [] t) →
            (∀ c ∈ cs, ∀ t ∈ c.argTypes, Typed.Typ.AppRefToDt tds [] t) →
            ∀ p' ∈ cs.foldl (fun s c => c.argTypes.foldl collectInTyp s) acc,
              ∀ t ∈ p'.2, Typed.Typ.AppRefToDt tds [] t := by
          intro cs
          induction cs with
          | nil => intro acc hacc _ p' hp'; exact hacc p' hp'
          | cons hd tl ih_l =>
            intro acc hacc hcs
            simp only [List.foldl_cons]
            apply ih_l
            · exact aux_inner hd.argTypes acc hacc
                (fun t ht => hcs hd List.mem_cons_self t ht)
            · intro c hc; exact hcs c (List.mem_cons_of_mem _ hc)
        let newCtors := dt.constructors.map fun c =>
          ({ c with argTypes := c.argTypes.map (Typ.instantiate subst) } :
            Constructor)
        have h_newCtors_AR : ∀ c ∈ newCtors, ∀ t ∈ c.argTypes,
            Typed.Typ.AppRefToDt tds [] t := by
          intro c hc t ht
          rw [List.mem_map] at hc
          obtain ⟨c0, hc0_mem, hc0_eq⟩ := hc
          subst hc0_eq
          rw [List.mem_map] at ht
          obtain ⟨t0, ht0_mem, ht0_eq⟩ := ht
          subst ht0_eq
          exact Typ.instantiate_preserves_AppRefToDt subst hsubst_AR hsubst_total
            (h_dt c0 hc0_mem t0 ht0_mem)
        exact aux newCtors _ hinv_pending h_newCtors_AR p hp
      · exact absurd hstep (by intro h; cases h)
    · cases hstep

/-- List foldlM lift of `concretizeDrainEntry_preserves_CtorArgsAppRefToDt`.
Mirrors `concretizeDrainEntry_list_foldlM_preserves_StrongNewNameShape`
(Shapes.lean:72) with `PendingArgsAppRefToDt` threaded as auxiliary. -/
theorem concretizeDrainEntry_list_foldlM_preserves_CtorArgsAppRefToDt
    {tds : Typed.Decls}
    (hCtor : Typed.Decls.AllCtorArgsAppRefToDt tds)
    (L : List (Global × Array Typ))
    (hLargs : ∀ entry ∈ L, ∀ t ∈ entry.2, Typed.Typ.AppRefToDt tds [] t)
    (state0 state' : DrainState)
    (hinv0 : state0.CtorArgsAppRefToDt tds)
    (hstep : L.foldlM (concretizeDrainEntry tds) state0 = .ok state') :
    state'.CtorArgsAppRefToDt tds := by
  induction L generalizing state0 with
  | nil =>
    simp only [List.foldlM, pure, Except.pure, Except.ok.injEq] at hstep
    rw [← hstep]; exact hinv0
  | cons hd tl ih =>
    simp only [List.foldlM, bind, Except.bind] at hstep
    split at hstep
    · cases hstep
    · rename_i s'' hs''
      have hhd_AR : ∀ t ∈ hd.2, Typed.Typ.AppRefToDt tds [] t :=
        hLargs hd List.mem_cons_self
      have htl_AR : ∀ entry ∈ tl, ∀ t ∈ entry.2, Typed.Typ.AppRefToDt tds [] t :=
        fun e he => hLargs e (List.mem_cons_of_mem _ he)
      have hinv1 : s''.CtorArgsAppRefToDt tds :=
        concretizeDrainEntry_preserves_CtorArgsAppRefToDt hCtor hinv0 hd hhd_AR hs''
      exact ih htl_AR s'' hinv1 hstep

/-- List foldlM lift of `concretizeDrainEntry_preserves_PendingArgsAppRefToDt`. -/
theorem concretizeDrainEntry_list_foldlM_preserves_PendingArgsAppRefToDt
    {tds : Typed.Decls}
    (hAll : Typed.Decls.AllAppRefToDt tds)
    (L : List (Global × Array Typ))
    (hLargs : ∀ entry ∈ L, ∀ t ∈ entry.2, Typed.Typ.AppRefToDt tds [] t)
    (state0 state' : DrainState)
    (hinv0 : state0.PendingArgsAppRefToDt tds)
    (hstep : L.foldlM (concretizeDrainEntry tds) state0 = .ok state') :
    state'.PendingArgsAppRefToDt tds := by
  induction L generalizing state0 with
  | nil =>
    simp only [List.foldlM, pure, Except.pure, Except.ok.injEq] at hstep
    rw [← hstep]; exact hinv0
  | cons hd tl ih =>
    simp only [List.foldlM, bind, Except.bind] at hstep
    split at hstep
    · cases hstep
    · rename_i s'' hs''
      have hhd_AR : ∀ t ∈ hd.2, Typed.Typ.AppRefToDt tds [] t :=
        hLargs hd List.mem_cons_self
      have htl_AR : ∀ entry ∈ tl, ∀ t ∈ entry.2, Typed.Typ.AppRefToDt tds [] t :=
        fun e he => hLargs e (List.mem_cons_of_mem _ he)
      have hinv1 : s''.PendingArgsAppRefToDt tds :=
        concretizeDrainEntry_preserves_PendingArgsAppRefToDt hAll hinv0 hd hhd_AR hs''
      exact ih htl_AR s'' hinv1 hstep

/-- Drain iter lift for `CtorArgsAppRefToDt`. Mirrors
`concretizeDrainIter_preserves_StrongNewNameShape` (Shapes.lean:92). -/
theorem concretizeDrainIter_preserves_CtorArgsAppRefToDt
    {tds : Typed.Decls}
    (hCtor : Typed.Decls.AllCtorArgsAppRefToDt tds)
    {state state' : DrainState}
    (hinv : state.CtorArgsAppRefToDt tds)
    (hpargs : state.PendingArgsAppRefToDt tds)
    (hstep : concretizeDrainIter tds state = .ok state') :
    state'.CtorArgsAppRefToDt tds := by
  unfold concretizeDrainIter at hstep
  rw [← Array.foldlM_toList] at hstep
  let state0 : DrainState := { state with pending := ∅ }
  have hinv0 : state0.CtorArgsAppRefToDt tds := hinv
  have hLargs : ∀ entry ∈ state.pending.toArray.toList,
      ∀ t ∈ entry.2, Typed.Typ.AppRefToDt tds [] t := by
    intro entry hentry t ht
    apply hpargs entry _ t ht
    rw [Array.mem_toList_iff] at hentry
    exact (Std.HashSet.mem_toArray.mp hentry)
  exact concretizeDrainEntry_list_foldlM_preserves_CtorArgsAppRefToDt hCtor
    state.pending.toArray.toList hLargs state0 state' hinv0 hstep

/-- Drain iter lift for `PendingArgsAppRefToDt`. -/
theorem concretizeDrainIter_preserves_PendingArgsAppRefToDt
    {tds : Typed.Decls}
    (hAll : Typed.Decls.AllAppRefToDt tds)
    {state state' : DrainState}
    (hpargs : state.PendingArgsAppRefToDt tds)
    (hstep : concretizeDrainIter tds state = .ok state') :
    state'.PendingArgsAppRefToDt tds := by
  unfold concretizeDrainIter at hstep
  rw [← Array.foldlM_toList] at hstep
  let state0 : DrainState := { state with pending := ∅ }
  have hinv0 : state0.PendingArgsAppRefToDt tds := by
    intro entry hentry
    exact (Std.HashSet.not_mem_empty hentry).elim
  have hLargs : ∀ entry ∈ state.pending.toArray.toList,
      ∀ t ∈ entry.2, Typed.Typ.AppRefToDt tds [] t := by
    intro entry hentry t ht
    apply hpargs entry _ t ht
    rw [Array.mem_toList_iff] at hentry
    exact (Std.HashSet.mem_toArray.mp hentry)
  exact concretizeDrainEntry_list_foldlM_preserves_PendingArgsAppRefToDt hAll
    state.pending.toArray.toList hLargs state0 state' hinv0 hstep

/-- Top concretizeDrain lift for `CtorArgsAppRefToDt`. Mirrors
`concretize_drain_preserves_StrongNewNameShape` (Shapes.lean:104). Threads
`PendingArgsAppRefToDt` as auxiliary. Sig amendment 2026-05-04: takes
`AllAppRefToDt` (broader bundle) since the threaded
`concretizeDrainIter_preserves_PendingArgsAppRefToDt` now needs it. -/
theorem concretize_drain_preserves_CtorArgsAppRefToDt
    {tds : Typed.Decls}
    (hAll : Typed.Decls.AllAppRefToDt tds)
    (fuel : Nat) (init : DrainState)
    (hinv : init.CtorArgsAppRefToDt tds)
    (hpargs_init : init.PendingArgsAppRefToDt tds)
    {drained : DrainState}
    (hdrain : concretizeDrain tds fuel init = .ok drained) :
    drained.CtorArgsAppRefToDt tds := by
  have hCtor : Typed.Decls.AllCtorArgsAppRefToDt tds := hAll.1
  induction fuel generalizing init with
  | zero =>
    unfold concretizeDrain at hdrain
    by_cases hpen : init.pending.isEmpty
    · simp only [hpen, if_true, pure, Except.pure, Except.ok.injEq] at hdrain
      rw [← hdrain]; exact hinv
    · simp [hpen] at hdrain
  | succ n ih =>
    unfold concretizeDrain at hdrain
    by_cases hpen : init.pending.isEmpty
    · simp only [hpen, if_true, pure, Except.pure, Except.ok.injEq] at hdrain
      rw [← hdrain]; exact hinv
    · simp only [hpen, if_false, Bool.false_eq_true] at hdrain
      simp only [bind, Except.bind] at hdrain
      split at hdrain
      · cases hdrain
      · rename_i state' hstate'
        have hinv' : state'.CtorArgsAppRefToDt tds :=
          concretizeDrainIter_preserves_CtorArgsAppRefToDt hCtor hinv hpargs_init hstate'
        have hpargs' : state'.PendingArgsAppRefToDt tds :=
          concretizeDrainIter_preserves_PendingArgsAppRefToDt hAll hpargs_init hstate'
        exact ih state' hinv' hpargs' hdrain

/-- Top concretizeDrain lift for `PendingArgsAppRefToDt`. -/
theorem concretize_drain_preserves_PendingArgsAppRefToDt
    {tds : Typed.Decls}
    (hAll : Typed.Decls.AllAppRefToDt tds)
    (fuel : Nat) (init : DrainState)
    (hpargs_init : init.PendingArgsAppRefToDt tds)
    {drained : DrainState}
    (hdrain : concretizeDrain tds fuel init = .ok drained) :
    drained.PendingArgsAppRefToDt tds := by
  induction fuel generalizing init with
  | zero =>
    unfold concretizeDrain at hdrain
    by_cases hpen : init.pending.isEmpty
    · simp only [hpen, if_true, pure, Except.pure, Except.ok.injEq] at hdrain
      rw [← hdrain]; exact hpargs_init
    · simp [hpen] at hdrain
  | succ n ih =>
    unfold concretizeDrain at hdrain
    by_cases hpen : init.pending.isEmpty
    · simp only [hpen, if_true, pure, Except.pure, Except.ok.injEq] at hdrain
      rw [← hdrain]; exact hpargs_init
    · simp only [hpen, if_false, Bool.false_eq_true] at hdrain
      simp only [bind, Except.bind] at hdrain
      split at hdrain
      · cases hdrain
      · rename_i state' hstate'
        have hpargs' : state'.PendingArgsAppRefToDt tds :=
          concretizeDrainIter_preserves_PendingArgsAppRefToDt hAll hpargs_init hstate'
        exact ih state' hpargs' hdrain

/-! #### `NewFnInputsAppRefToDt` / `NewFnOutputAppRefToDt` drain chain (4 levels).

Mirrors the `CtorArgsAppRefToDt` chain but for `newFunctions`. The drain's
`.function` arm pushes a newFn whose `inputs` and `output` are obtained via
`Typ.instantiate subst` of the source template's inputs/output; preservation
follows from `Typ.instantiate_preserves_AppRefToDt` once the source-template
positions are AppRefToDt-safe (`AllFnInputs/OutputAppRefToDt` precondition)
and the substitution image is AppRefToDt-safe (via `PendingArgsAppRefToDt`). -/

/-- Init: empty newFunctions vacuously satisfies. -/
theorem DrainState.NewFnInputsAppRefToDt.init
    (tds : Typed.Decls) (pending : Std.HashSet (Global × Array Typ)) :
    DrainState.NewFnInputsAppRefToDt tds
      { pending, seen := {}, mono := {},
        newFunctions := #[], newDataTypes := #[] } := by
  intro f hmem
  simp only [Array.not_mem_empty] at hmem

theorem DrainState.NewFnOutputAppRefToDt.init
    (tds : Typed.Decls) (pending : Std.HashSet (Global × Array Typ)) :
    DrainState.NewFnOutputAppRefToDt tds
      { pending, seen := {}, mono := {},
        newFunctions := #[], newDataTypes := #[] } := by
  intro f hmem
  simp only [Array.not_mem_empty] at hmem

/-- Drain entry preservation for `NewFnInputsAppRefToDt`. Three arms:
* `.function`: pushes `newFn` with `inputs := f.inputs.map (l, t) ↦ (l, instantiate subst t)`.
  Each new input snd is AppRefToDt by `instantiate_preserves_AppRefToDt`
  (source template position via `AllFnInputsAppRefToDt`; subst image via
  `PendingArgsAppRefToDt`).
* `.dataType`: doesn't touch `newFunctions`, trivially preserves.
* throw arm: contradicts `hstep` success. -/
theorem concretizeDrainEntry_preserves_NewFnInputsAppRefToDt
    {tds : Typed.Decls}
    (hFnIn : Typed.Decls.AllFnInputsAppRefToDt tds)
    {state state' : DrainState}
    (hinv : state.NewFnInputsAppRefToDt tds)
    (entry : Global × Array Typ)
    (hpargs : ∀ t ∈ entry.2, Typed.Typ.AppRefToDt tds [] t)
    (hstep : concretizeDrainEntry tds state entry = .ok state') :
    state'.NewFnInputsAppRefToDt tds := by
  unfold concretizeDrainEntry at hstep
  simp only [bind, Except.bind, pure, Except.pure] at hstep
  by_cases hseen : state.seen.contains (entry.1, entry.2)
  · simp [hseen] at hstep
    rw [← hstep]; exact hinv
  · simp [hseen] at hstep
    split at hstep
    · -- function arm — pushes newFn.
      rename_i f hf_get
      split at hstep
      · simp only [Except.ok.injEq] at hstep
        rw [← hstep]
        let subst := mkParamSubst f.params entry.2
        have hsubst_AR : ∀ g t', subst g = some t' →
            Typed.Typ.AppRefToDt tds [] t' :=
          fun g t' h => hpargs t' (mkParamSubst_some_mem _ _ h)
        have hsubst_total : ∀ g, (∃ p ∈ f.params, g = Global.init p) →
            ∃ t', subst g = some t' := by
          intro g hin
          have h_arity : entry.2.size = f.params.length := by
            rename_i hsize_eq
            have h := (by simpa [beq_iff_eq] using hsize_eq : f.params.length = entry.2.size)
            exact h.symm
          exact mkParamSubst_total_on_params f.params entry.2 h_arity hin
        intro f' hf'_mem lt' hlt'_mem
        rcases Array.mem_push.mp hf'_mem with hin | heq
        · exact hinv f' hin lt' hlt'_mem
        · -- f' = newFn: inputs = f.inputs.map (instantiate subst).
          subst heq
          simp only at hlt'_mem
          rw [List.mem_map] at hlt'_mem
          obtain ⟨lt0, hlt0_mem, hlt0_eq⟩ := hlt'_mem
          subst hlt0_eq
          have h_lt0_AR : Typed.Typ.AppRefToDt tds f.params lt0.2 :=
            hFnIn entry.1 f hf_get lt0 hlt0_mem
          exact Typ.instantiate_preserves_AppRefToDt subst hsubst_AR hsubst_total h_lt0_AR
      · exact absurd hstep (by intro h; cases h)
    · -- dataType arm — newFunctions unchanged.
      rename_i dt hdt_get
      split at hstep
      · simp only [Except.ok.injEq] at hstep
        rw [← hstep]
        intro f' hf'_mem lt' hlt'_mem
        exact hinv f' hf'_mem lt' hlt'_mem
      · exact absurd hstep (by intro h; cases h)
    · cases hstep

theorem concretizeDrainEntry_preserves_NewFnOutputAppRefToDt
    {tds : Typed.Decls}
    (hFnOut : Typed.Decls.AllFnOutputAppRefToDt tds)
    {state state' : DrainState}
    (hinv : state.NewFnOutputAppRefToDt tds)
    (entry : Global × Array Typ)
    (hpargs : ∀ t ∈ entry.2, Typed.Typ.AppRefToDt tds [] t)
    (hstep : concretizeDrainEntry tds state entry = .ok state') :
    state'.NewFnOutputAppRefToDt tds := by
  unfold concretizeDrainEntry at hstep
  simp only [bind, Except.bind, pure, Except.pure] at hstep
  by_cases hseen : state.seen.contains (entry.1, entry.2)
  · simp [hseen] at hstep
    rw [← hstep]; exact hinv
  · simp [hseen] at hstep
    split at hstep
    · rename_i f hf_get
      split at hstep
      · simp only [Except.ok.injEq] at hstep
        rw [← hstep]
        let subst := mkParamSubst f.params entry.2
        have hsubst_AR : ∀ g t', subst g = some t' →
            Typed.Typ.AppRefToDt tds [] t' :=
          fun g t' h => hpargs t' (mkParamSubst_some_mem _ _ h)
        have hsubst_total : ∀ g, (∃ p ∈ f.params, g = Global.init p) →
            ∃ t', subst g = some t' := by
          intro g hin
          have h_arity : entry.2.size = f.params.length := by
            rename_i hsize_eq
            have h := (by simpa [beq_iff_eq] using hsize_eq : f.params.length = entry.2.size)
            exact h.symm
          exact mkParamSubst_total_on_params f.params entry.2 h_arity hin
        intro f' hf'_mem
        rcases Array.mem_push.mp hf'_mem with hin | heq
        · exact hinv f' hin
        · subst heq
          simp only
          have h_out_AR : Typed.Typ.AppRefToDt tds f.params f.output :=
            hFnOut entry.1 f hf_get
          exact Typ.instantiate_preserves_AppRefToDt subst hsubst_AR hsubst_total h_out_AR
      · exact absurd hstep (by intro h; cases h)
    · rename_i dt hdt_get
      split at hstep
      · simp only [Except.ok.injEq] at hstep
        rw [← hstep]
        intro f' hf'_mem
        exact hinv f' hf'_mem
      · exact absurd hstep (by intro h; cases h)
    · cases hstep

/-- List-foldlM lift for `NewFnInputsAppRefToDt`. -/
theorem concretizeDrainEntry_list_foldlM_preserves_NewFnInputsAppRefToDt
    {tds : Typed.Decls}
    (hFnIn : Typed.Decls.AllFnInputsAppRefToDt tds)
    (L : List (Global × Array Typ))
    (hLargs : ∀ entry ∈ L, ∀ t ∈ entry.2, Typed.Typ.AppRefToDt tds [] t)
    (state0 state' : DrainState)
    (hinv0 : state0.NewFnInputsAppRefToDt tds)
    (hstep : L.foldlM (concretizeDrainEntry tds) state0 = .ok state') :
    state'.NewFnInputsAppRefToDt tds := by
  induction L generalizing state0 with
  | nil =>
    simp only [List.foldlM, pure, Except.pure, Except.ok.injEq] at hstep
    rw [← hstep]; exact hinv0
  | cons hd tl ih =>
    simp only [List.foldlM, bind, Except.bind] at hstep
    split at hstep
    · cases hstep
    · rename_i s'' hs''
      have hhd_AR : ∀ t ∈ hd.2, Typed.Typ.AppRefToDt tds [] t :=
        hLargs hd List.mem_cons_self
      have htl_AR : ∀ entry ∈ tl, ∀ t ∈ entry.2, Typed.Typ.AppRefToDt tds [] t :=
        fun e he => hLargs e (List.mem_cons_of_mem _ he)
      have hinv1 : s''.NewFnInputsAppRefToDt tds :=
        concretizeDrainEntry_preserves_NewFnInputsAppRefToDt hFnIn hinv0 hd hhd_AR hs''
      exact ih htl_AR s'' hinv1 hstep

theorem concretizeDrainEntry_list_foldlM_preserves_NewFnOutputAppRefToDt
    {tds : Typed.Decls}
    (hFnOut : Typed.Decls.AllFnOutputAppRefToDt tds)
    (L : List (Global × Array Typ))
    (hLargs : ∀ entry ∈ L, ∀ t ∈ entry.2, Typed.Typ.AppRefToDt tds [] t)
    (state0 state' : DrainState)
    (hinv0 : state0.NewFnOutputAppRefToDt tds)
    (hstep : L.foldlM (concretizeDrainEntry tds) state0 = .ok state') :
    state'.NewFnOutputAppRefToDt tds := by
  induction L generalizing state0 with
  | nil =>
    simp only [List.foldlM, pure, Except.pure, Except.ok.injEq] at hstep
    rw [← hstep]; exact hinv0
  | cons hd tl ih =>
    simp only [List.foldlM, bind, Except.bind] at hstep
    split at hstep
    · cases hstep
    · rename_i s'' hs''
      have hhd_AR : ∀ t ∈ hd.2, Typed.Typ.AppRefToDt tds [] t :=
        hLargs hd List.mem_cons_self
      have htl_AR : ∀ entry ∈ tl, ∀ t ∈ entry.2, Typed.Typ.AppRefToDt tds [] t :=
        fun e he => hLargs e (List.mem_cons_of_mem _ he)
      have hinv1 : s''.NewFnOutputAppRefToDt tds :=
        concretizeDrainEntry_preserves_NewFnOutputAppRefToDt hFnOut hinv0 hd hhd_AR hs''
      exact ih htl_AR s'' hinv1 hstep

/-- Drain iter lift for `NewFnInputsAppRefToDt`. -/
theorem concretizeDrainIter_preserves_NewFnInputsAppRefToDt
    {tds : Typed.Decls}
    (hFnIn : Typed.Decls.AllFnInputsAppRefToDt tds)
    {state state' : DrainState}
    (hinv : state.NewFnInputsAppRefToDt tds)
    (hpargs : state.PendingArgsAppRefToDt tds)
    (hstep : concretizeDrainIter tds state = .ok state') :
    state'.NewFnInputsAppRefToDt tds := by
  unfold concretizeDrainIter at hstep
  rw [← Array.foldlM_toList] at hstep
  let state0 : DrainState := { state with pending := ∅ }
  have hinv0 : state0.NewFnInputsAppRefToDt tds := hinv
  have hLargs : ∀ entry ∈ state.pending.toArray.toList,
      ∀ t ∈ entry.2, Typed.Typ.AppRefToDt tds [] t := by
    intro entry hentry t ht
    apply hpargs entry _ t ht
    rw [Array.mem_toList_iff] at hentry
    exact (Std.HashSet.mem_toArray.mp hentry)
  exact concretizeDrainEntry_list_foldlM_preserves_NewFnInputsAppRefToDt hFnIn
    state.pending.toArray.toList hLargs state0 state' hinv0 hstep

theorem concretizeDrainIter_preserves_NewFnOutputAppRefToDt
    {tds : Typed.Decls}
    (hFnOut : Typed.Decls.AllFnOutputAppRefToDt tds)
    {state state' : DrainState}
    (hinv : state.NewFnOutputAppRefToDt tds)
    (hpargs : state.PendingArgsAppRefToDt tds)
    (hstep : concretizeDrainIter tds state = .ok state') :
    state'.NewFnOutputAppRefToDt tds := by
  unfold concretizeDrainIter at hstep
  rw [← Array.foldlM_toList] at hstep
  let state0 : DrainState := { state with pending := ∅ }
  have hinv0 : state0.NewFnOutputAppRefToDt tds := hinv
  have hLargs : ∀ entry ∈ state.pending.toArray.toList,
      ∀ t ∈ entry.2, Typed.Typ.AppRefToDt tds [] t := by
    intro entry hentry t ht
    apply hpargs entry _ t ht
    rw [Array.mem_toList_iff] at hentry
    exact (Std.HashSet.mem_toArray.mp hentry)
  exact concretizeDrainEntry_list_foldlM_preserves_NewFnOutputAppRefToDt hFnOut
    state.pending.toArray.toList hLargs state0 state' hinv0 hstep

/-- Top-level drain lift for `NewFnInputsAppRefToDt`. Threads
`PendingArgsAppRefToDt` through; its preservation requires the bundled
`AllAppRefToDt` (consumed by `concretizeDrainIter_preserves_PendingArgsAppRefToDt`). -/
theorem concretize_drain_preserves_NewFnInputsAppRefToDt
    {tds : Typed.Decls}
    (hAll : Typed.Decls.AllAppRefToDt tds)
    (hFnIn : Typed.Decls.AllFnInputsAppRefToDt tds)
    (fuel : Nat) (init : DrainState)
    (hinv : init.NewFnInputsAppRefToDt tds)
    (hpargs_init : init.PendingArgsAppRefToDt tds)
    {drained : DrainState}
    (hdrain : concretizeDrain tds fuel init = .ok drained) :
    drained.NewFnInputsAppRefToDt tds := by
  induction fuel generalizing init with
  | zero =>
    unfold concretizeDrain at hdrain
    by_cases hpen : init.pending.isEmpty
    · simp only [hpen, if_true, pure, Except.pure, Except.ok.injEq] at hdrain
      rw [← hdrain]; exact hinv
    · simp [hpen] at hdrain
  | succ n ih =>
    unfold concretizeDrain at hdrain
    by_cases hpen : init.pending.isEmpty
    · simp only [hpen, if_true, pure, Except.pure, Except.ok.injEq] at hdrain
      rw [← hdrain]; exact hinv
    · simp only [hpen, if_false, Bool.false_eq_true] at hdrain
      simp only [bind, Except.bind] at hdrain
      split at hdrain
      · cases hdrain
      · rename_i state' hstate'
        have hinv' : state'.NewFnInputsAppRefToDt tds :=
          concretizeDrainIter_preserves_NewFnInputsAppRefToDt hFnIn hinv hpargs_init hstate'
        have hpargs' : state'.PendingArgsAppRefToDt tds :=
          concretizeDrainIter_preserves_PendingArgsAppRefToDt hAll hpargs_init hstate'
        exact ih state' hinv' hpargs' hdrain

theorem concretize_drain_preserves_NewFnOutputAppRefToDt
    {tds : Typed.Decls}
    (hAll : Typed.Decls.AllAppRefToDt tds)
    (hFnOut : Typed.Decls.AllFnOutputAppRefToDt tds)
    (fuel : Nat) (init : DrainState)
    (hinv : init.NewFnOutputAppRefToDt tds)
    (hpargs_init : init.PendingArgsAppRefToDt tds)
    {drained : DrainState}
    (hdrain : concretizeDrain tds fuel init = .ok drained) :
    drained.NewFnOutputAppRefToDt tds := by
  induction fuel generalizing init with
  | zero =>
    unfold concretizeDrain at hdrain
    by_cases hpen : init.pending.isEmpty
    · simp only [hpen, if_true, pure, Except.pure, Except.ok.injEq] at hdrain
      rw [← hdrain]; exact hinv
    · simp [hpen] at hdrain
  | succ n ih =>
    unfold concretizeDrain at hdrain
    by_cases hpen : init.pending.isEmpty
    · simp only [hpen, if_true, pure, Except.pure, Except.ok.injEq] at hdrain
      rw [← hdrain]; exact hinv
    · simp only [hpen, if_false, Bool.false_eq_true] at hdrain
      simp only [bind, Except.bind] at hdrain
      split at hdrain
      · cases hdrain
      · rename_i state' hstate'
        have hinv' : state'.NewFnOutputAppRefToDt tds :=
          concretizeDrainIter_preserves_NewFnOutputAppRefToDt hFnOut hinv hpargs_init hstate'
        have hpargs' : state'.PendingArgsAppRefToDt tds :=
          concretizeDrainIter_preserves_PendingArgsAppRefToDt hAll hpargs_init hstate'
        exact ih state' hinv' hpargs' hdrain

end RefClosedBody

/-- `concretize` output is ref-closed: every `.ref g` in `cd`'s types
resolves to a `.dataType g` in `cd`.

Takes `hDtNameIsKey` and `hCtorPresent` as explicit hypotheses (discharged
at call sites via `checkAndSimplify_preserves_dtNameIsKey` /
`checkAndSimplify_preserves_ctorPresent` in `CompilerProgress`, which is
downstream of this file). `hdt_params_empty`, `hNewDtBridge`, and
`hNewFnBridge` are derived internally using `CheckSound` +
`StrongNewNameShape`. The L1 / L3 components remain `sorry` pending their own
upstream moves. -/
theorem concretize_produces_refClosed
    {t : Source.Toplevel} {tds : Typed.Decls} {cd : Concrete.Decls}
    (hmono : FullyMonomorphic t)
    (hts : t.checkAndSimplify = .ok tds)
    (hconc : tds.concretize = .ok cd)
    (hunique : Typed.Decls.ConcretizeUniqueNames tds)
    (hDtNameIsKey : ∀ (key : Global) (dt : DataType),
      (key, Typed.Declaration.dataType dt) ∈ tds.pairs.toList → key = dt.name)
    (hCtorPresent : ∀ (dtkey : Global) (dt : DataType) (c : Constructor),
      (dtkey, Typed.Declaration.dataType dt) ∈ tds.pairs.toList →
      c ∈ dt.constructors →
      ∃ cc, (dt.name.pushNamespace c.nameHead,
        Typed.Declaration.constructor dt cc) ∈ tds.pairs.toList) :
    Concrete.Decls.RefClosed cd := by
  -- Extract `decls` witness from `hts` so we can invoke CheckSound lemmas.
  have ⟨decls, hdecls, _hrest⟩ :
      ∃ decls, t.mkDecls = .ok decls ∧ True := by
    unfold Source.Toplevel.checkAndSimplify at hts
    simp only [bind, Except.bind] at hts
    split at hts
    · cases hts
    rename_i srcDecls hmk
    exact ⟨srcDecls, hmk, trivial⟩
  -- Derive `hdt_params_empty` from CheckSound.
  have hdt_params_empty : ∀ g dt, tds.getByKey g = some (.dataType dt) → dt.params = [] :=
    typedDecls_dt_params_empty_of_fullyMonomorphic hmono hdecls hts
  have hfn_params_empty : ∀ g f, tds.getByKey g = some (.function f) → f.params = [] :=
    typedDecls_params_empty_of_fullyMonomorphic hmono hdecls hts
  -- Derive `hNewDtBridge` / `hNewFnBridge` inline (proof bodies match
  -- `CompilerProgress.newDtBridge_derive` / `newFnBridge_derive`).
  have hNewDtBridge : ∀ {drained : DrainState},
      concretizeDrain tds (concretizeDrainFuel tds)
          { pending := concretizeSeed tds, seen := {}, mono := {},
            newFunctions := #[], newDataTypes := #[] } = .ok drained →
      NewDtBridge tds drained.newDataTypes := by
    intro drained hdrain dt hdt_mem
    have hinit : DrainState.StrongNewNameShape tds _ :=
      DrainState.StrongNewNameShape.init tds (concretizeSeed tds)
    have hfinal := concretize_drain_preserves_StrongNewNameShape _ _ hinit hdrain
    obtain ⟨g, args, dt_orig, hname, hget, hargs_sz, hctors⟩ := hfinal.2 dt hdt_mem
    have hdt_orig_params := hdt_params_empty g dt_orig hget
    have hargs_zero : args.size = 0 := by rw [hargs_sz, hdt_orig_params]; rfl
    have hargs_empty : args = #[] := Array.size_eq_zero_iff.mp hargs_zero
    have hname_eq : dt.name = g := by
      rw [hname, hargs_empty]; exact concretizeName_empty_args g
    exact ⟨g, dt_orig, hget, hname_eq, hctors⟩
  have hNewFnBridge : ∀ {drained : DrainState},
      concretizeDrain tds (concretizeDrainFuel tds)
          { pending := concretizeSeed tds, seen := {}, mono := {},
            newFunctions := #[], newDataTypes := #[] } = .ok drained →
      NewFnBridge tds drained.newFunctions := by
    intro drained hdrain f hf_mem
    have hinit : DrainState.StrongNewNameShape tds _ :=
      DrainState.StrongNewNameShape.init tds (concretizeSeed tds)
    have hfinal := concretize_drain_preserves_StrongNewNameShape _ _ hinit hdrain
    obtain ⟨g, args, f_orig, hname, hget, hargs_sz⟩ := hfinal.1 f hf_mem
    have hf_orig_params := hfn_params_empty g f_orig hget
    have hargs_zero : args.size = 0 := by rw [hargs_sz, hf_orig_params]; rfl
    have hargs_empty : args = #[] := Array.size_eq_zero_iff.mp hargs_zero
    have hname_eq : f.name = g := by
      rw [hname, hargs_empty]; exact concretizeName_empty_args g
    exact ⟨g, f_orig, hget, hname_eq⟩
  exact RefClosedBody.concretize_produces_refClosed hmono hts hconc hunique
    hdt_params_empty hCtorPresent hDtNameIsKey hNewDtBridge hNewFnBridge

/-! ### Entry-restricted RefClosed bridge.

The fully-monomorphic closure of `Concrete.Decls.RefClosed cd` (the theorem
`concretize_produces_refClosed` above) routes through `AllRefsAreDtKeys tds`
(the L1 layer), which is structurally false in the presence of polymorphic
templates: tds carries `.app g args` types whose targets are template names,
not dt-keys. For the entry-restricted variant — invoked from
`compile_correct_concRetFnFree_entry` with `WellFormed t` only — we bypass
the universal L1 layer and instead reason directly on `cd`. -/

/-! ### Source-side AppRefToDt lift (placed before umbrella for forward-ref).

The drain-invariant chain `concretize_produces_CtorArgsAppRefToDt` is needed
inside the umbrella's `.ctor`-newDt arm. -/

theorem AllCtorArgsAppRefToDt_of_wellFormed
    {t : Source.Toplevel} {decls : Source.Decls} {tds : Typed.Decls}
    (hwf : WellFormed t) (hdecls : t.mkDecls = .ok decls)
    (hts : t.checkAndSimplify = .ok tds) :
    Typed.Decls.AllCtorArgsAppRefToDt tds := by
  intro g dt c hget hc t ht
  have hsrc_get : decls.getByKey g = some (.dataType dt) :=
    checkAndSimplify_dt_in_source hdecls hts hget
  have hpair : (g, Source.Declaration.dataType dt) ∈ decls.pairs.toList :=
    IndexMap.mem_pairs_of_getByKey _ _ _ hsrc_get
  have hwfd : wellFormedDecls decls = .ok () :=
    checkAndSimplify_implies_wellFormedDecls hdecls hts
  have hdt_key_name : ∀ k dt', decls.getByKey k = some (.dataType dt') → k = dt'.name :=
    mkDecls_dt_key_is_name hdecls
  obtain ⟨_vis, _vis', _hfresh, hstep⟩ :=
    wellFormedDecls_reflect_dataType_fresh hdt_key_name hwfd hpair
  have hwfT : wellFormedDecls.wellFormedType decls dt.params t = .ok () :=
    wellFormedDecls_reflect_dataType _hfresh hstep c hc t ht
  -- Source-side reflection (now polymorphic-aware via the `params` parameter).
  have hSrc : SrcTypRefsAreDtKeys decls dt.params t :=
    SrcTypRefsAreDtKeys_of_wellFormedType decls dt.params t hwfT
  -- Lift to typed-side AppRefToDt under the same `dt.params` context.
  have h_dt_lift : ∀ g, (∃ dt_src, decls.getByKey g = some (.dataType dt_src)) →
      ∃ dt_td, tds.getByKey g = some (.dataType dt_td) := by
    intro g ⟨dt_src, hg_src⟩
    obtain ⟨dt_td, hg_td⟩ := checkAndSimplify_src_dt_to_td hdecls hts hg_src
    exact ⟨dt_td, hg_td⟩
  have h_dt_params_lift : ∀ g,
      (∃ dt_src, decls.getByKey g = some (.dataType dt_src) ∧ dt_src.params = []) →
      ∃ dt_td, tds.getByKey g = some (.dataType dt_td) ∧ dt_td.params = [] := by
    intro g ⟨dt_src, hg_src, hparams⟩
    obtain ⟨dt_td, hg_td⟩ := checkAndSimplify_src_dt_to_td hdecls hts hg_src
    -- TdDtParamsMatchP: typed dt at g maps back to source dt at g (same dt).
    have hP := TdDtParamsMatchP_checkAndSimplify hdecls hts
    have hsrc' : decls.getByKey g = some (.dataType dt_td) := hP g dt_td hg_td
    have hdt_eq : dt_src = dt_td := by
      rw [hg_src] at hsrc'
      cases hsrc'; rfl
    exact ⟨dt_td, hg_td, hdt_eq ▸ hparams⟩
  exact RefClosedBody.AppRefToDt_of_SrcTypRefsAreDtKeys
    h_dt_lift h_dt_params_lift hSrc

/-! ### Source-side AppRefToDt lifts for fn inputs/output.

NB: `concretize_produces_CtorArgsAppRefToDt` was previously here but was
moved BELOW `AllAppRefToDt_of_wellFormed` (sig amendment 2026-05-03,
Defect 3) so it can use the bundle helper. -/

theorem AllFnInputsAppRefToDt_of_wellFormed
    {t : Source.Toplevel} {decls : Source.Decls} {tds : Typed.Decls}
    (hwf : WellFormed t) (hdecls : t.mkDecls = .ok decls)
    (hts : t.checkAndSimplify = .ok tds) :
    Typed.Decls.AllFnInputsAppRefToDt tds := by
  intro g f hget lt hlt
  -- Source-side: the typed function corresponds to a source function via FnMatchP.
  have hP := FnMatchP_checkAndSimplify hdecls hts
  obtain ⟨src_f_decl, hsrc_decl, hinputs_eq⟩ := (hP g).1 f hget
  have hwf_src := checkAndSimplify_implies_wellFormedDecls hdecls hts
  have hsrc_pair :
      (g, Source.Declaration.function src_f_decl) ∈ decls.pairs.toList :=
    IndexMap.mem_pairs_of_getByKey _ _ _ hsrc_decl
  obtain ⟨_vis, _vis', hwf_step⟩ :=
    wellFormedDecls_reflect_pair hwf_src g (.function src_f_decl) hsrc_pair
  have hwf_pair := wellFormedDecls_reflect_function hwf_step
  -- src_f_decl.inputs = f.inputs (FnMatchP equates inputs).
  have hsrc_lt_in_decl : lt ∈ src_f_decl.inputs := by
    rw [hinputs_eq] at hlt
    exact hlt
  have hwf_t : wellFormedDecls.wellFormedType decls src_f_decl.params lt.2 = .ok () :=
    hwf_pair.2 lt hsrc_lt_in_decl
  -- Source-side reflection (polymorphic-aware via the `params` parameter).
  have hSrc : SrcTypRefsAreDtKeys decls src_f_decl.params lt.2 :=
    SrcTypRefsAreDtKeys_of_wellFormedType decls src_f_decl.params lt.2 hwf_t
  -- Typed `f.params = src_f_decl.params` (`checkFunction` threads params unchanged,
  -- `simplifyDecls` only rewrites bodies).
  have hfp_eq : f.params = src_f_decl.params :=
    checkAndSimplify_preserves_fn_params hdecls hts hsrc_decl hget
  rw [hfp_eq]
  have h_dt_lift : ∀ g, (∃ dt_src, decls.getByKey g = some (.dataType dt_src)) →
      ∃ dt_td, tds.getByKey g = some (.dataType dt_td) := by
    intro g ⟨dt_src, hg_src⟩
    obtain ⟨dt_td, hg_td⟩ := checkAndSimplify_src_dt_to_td hdecls hts hg_src
    exact ⟨dt_td, hg_td⟩
  have h_dt_params_lift : ∀ g,
      (∃ dt_src, decls.getByKey g = some (.dataType dt_src) ∧ dt_src.params = []) →
      ∃ dt_td, tds.getByKey g = some (.dataType dt_td) ∧ dt_td.params = [] := by
    intro g ⟨dt_src, hg_src, hparams⟩
    obtain ⟨dt_td, hg_td⟩ := checkAndSimplify_src_dt_to_td hdecls hts hg_src
    have hP := TdDtParamsMatchP_checkAndSimplify hdecls hts
    have hsrc' : decls.getByKey g = some (.dataType dt_td) := hP g dt_td hg_td
    have hdt_eq : dt_src = dt_td := by
      rw [hg_src] at hsrc'
      cases hsrc'; rfl
    exact ⟨dt_td, hg_td, hdt_eq ▸ hparams⟩
  exact RefClosedBody.AppRefToDt_of_SrcTypRefsAreDtKeys
    h_dt_lift h_dt_params_lift hSrc

theorem AllFnOutputAppRefToDt_of_wellFormed
    {t : Source.Toplevel} {decls : Source.Decls} {tds : Typed.Decls}
    (hwf : WellFormed t) (hdecls : t.mkDecls = .ok decls)
    (hts : t.checkAndSimplify = .ok tds) :
    Typed.Decls.AllFnOutputAppRefToDt tds := by
  intro g f hget
  have hP := FnMatchP_checkAndSimplify hdecls hts
  obtain ⟨src_f_decl, hsrc_decl, _hinputs_eq⟩ := (hP g).1 f hget
  have hwf_src := checkAndSimplify_implies_wellFormedDecls hdecls hts
  have hsrc_pair :
      (g, Source.Declaration.function src_f_decl) ∈ decls.pairs.toList :=
    IndexMap.mem_pairs_of_getByKey _ _ _ hsrc_decl
  obtain ⟨_vis, _vis', hwf_step⟩ :=
    wellFormedDecls_reflect_pair hwf_src g (.function src_f_decl) hsrc_pair
  have hwf_pair := wellFormedDecls_reflect_function hwf_step
  have houtput_eq : f.output = src_f_decl.output :=
    checkAndSimplify_preserves_output hdecls hts hsrc_decl hget
  rw [houtput_eq]
  have hwf_t : wellFormedDecls.wellFormedType decls src_f_decl.params src_f_decl.output
      = .ok () := hwf_pair.1
  -- Source-side reflection (polymorphic-aware via the `params` parameter).
  have hSrc : SrcTypRefsAreDtKeys decls src_f_decl.params src_f_decl.output :=
    SrcTypRefsAreDtKeys_of_wellFormedType decls src_f_decl.params src_f_decl.output hwf_t
  have hfp_eq : f.params = src_f_decl.params :=
    checkAndSimplify_preserves_fn_params hdecls hts hsrc_decl hget
  rw [hfp_eq]
  have h_dt_lift : ∀ g, (∃ dt_src, decls.getByKey g = some (.dataType dt_src)) →
      ∃ dt_td, tds.getByKey g = some (.dataType dt_td) := by
    intro g ⟨dt_src, hg_src⟩
    obtain ⟨dt_td, hg_td⟩ := checkAndSimplify_src_dt_to_td hdecls hts hg_src
    exact ⟨dt_td, hg_td⟩
  have h_dt_params_lift : ∀ g,
      (∃ dt_src, decls.getByKey g = some (.dataType dt_src) ∧ dt_src.params = []) →
      ∃ dt_td, tds.getByKey g = some (.dataType dt_td) ∧ dt_td.params = [] := by
    intro g ⟨dt_src, hg_src, hparams⟩
    obtain ⟨dt_td, hg_td⟩ := checkAndSimplify_src_dt_to_td hdecls hts hg_src
    have hP := TdDtParamsMatchP_checkAndSimplify hdecls hts
    have hsrc' : decls.getByKey g = some (.dataType dt_td) := hP g dt_td hg_td
    have hdt_eq : dt_src = dt_td := by
      rw [hg_src] at hsrc'
      cases hsrc'; rfl
    exact ⟨dt_td, hg_td, hdt_eq ▸ hparams⟩
  exact RefClosedBody.AppRefToDt_of_SrcTypRefsAreDtKeys
    h_dt_lift h_dt_params_lift hSrc

/-- Bundled `AllAppRefToDt` from `WellFormed`. Composes the three F=0
narrow lifts (`AllCtorArgsAppRefToDt + AllFnInputsAppRefToDt +
AllFnOutputAppRefToDt`) plus the body-cluster lift sourced from the
`WellFormed.bodyAppRefToDt` field (added 2026-05-04). Used to discharge
the broadened premise of `DrainState.PendingArgsAppRefToDt.init` (sig
amendment 2026-05-03, Defect 3). -/
theorem AllAppRefToDt_of_wellFormed
    {t : Source.Toplevel} {decls : Source.Decls} {tds : Typed.Decls}
    (hwf : WellFormed t) (hdecls : t.mkDecls = .ok decls)
    (hts : t.checkAndSimplify = .ok tds) :
    Typed.Decls.AllAppRefToDt tds :=
  ⟨AllCtorArgsAppRefToDt_of_wellFormed hwf hdecls hts,
   AllFnInputsAppRefToDt_of_wellFormed hwf hdecls hts,
   AllFnOutputAppRefToDt_of_wellFormed hwf hdecls hts,
   fun g f hget => hwf.bodyAppRefToDt tds hts g f hget⟩

/-- Drain output: `CtorArgsAppRefToDt` invariant on `drained.newDataTypes`.
Position previously above `AllFnInputs/Output_of_wellFormed`; moved here
(sig amendment 2026-05-03, Defect 3) so it can use the bundled
`AllAppRefToDt_of_wellFormed` to discharge `PendingArgsAppRefToDt.init`'s
broadened premise. -/
theorem concretize_produces_CtorArgsAppRefToDt
    {t : Source.Toplevel} {decls : Source.Decls} {tds : Typed.Decls}
    (hwf : WellFormed t)
    (hdecls : t.mkDecls = .ok decls)
    (hts : t.checkAndSimplify = .ok tds)
    {drained : DrainState}
    (hdrain : concretizeDrain tds (concretizeDrainFuel tds)
      { pending := concretizeSeed tds, seen := {}, mono := {},
        newFunctions := #[], newDataTypes := #[] } = .ok drained) :
    drained.CtorArgsAppRefToDt tds := by
  have hCtor : Typed.Decls.AllCtorArgsAppRefToDt tds :=
    AllCtorArgsAppRefToDt_of_wellFormed hwf hdecls hts
  -- Sig amendment 2026-05-03 (Defect 3): broadened premise.
  have hAll : Typed.Decls.AllAppRefToDt tds :=
    AllAppRefToDt_of_wellFormed hwf hdecls hts
  have hinit_ctor :
      DrainState.CtorArgsAppRefToDt tds
        { pending := concretizeSeed tds, seen := {}, mono := {},
          newFunctions := #[], newDataTypes := #[] } :=
    RefClosedBody.DrainState.CtorArgsAppRefToDt.init tds (concretizeSeed tds)
  have hinit_pargs :
      DrainState.PendingArgsAppRefToDt tds
        { pending := concretizeSeed tds, seen := {}, mono := {},
          newFunctions := #[], newDataTypes := #[] } :=
    RefClosedBody.DrainState.PendingArgsAppRefToDt.init hAll
  exact RefClosedBody.concretize_drain_preserves_CtorArgsAppRefToDt
    hAll _ _ hinit_ctor hinit_pargs hdrain

theorem concretize_produces_NewFnInputsAppRefToDt
    {t : Source.Toplevel} {decls : Source.Decls} {tds : Typed.Decls}
    (hwf : WellFormed t)
    (hdecls : t.mkDecls = .ok decls)
    (hts : t.checkAndSimplify = .ok tds)
    {drained : DrainState}
    (hdrain : concretizeDrain tds (concretizeDrainFuel tds)
      { pending := concretizeSeed tds, seen := {}, mono := {},
        newFunctions := #[], newDataTypes := #[] } = .ok drained) :
    drained.NewFnInputsAppRefToDt tds := by
  have hCtor : Typed.Decls.AllCtorArgsAppRefToDt tds :=
    AllCtorArgsAppRefToDt_of_wellFormed hwf hdecls hts
  have hFnIn : Typed.Decls.AllFnInputsAppRefToDt tds :=
    AllFnInputsAppRefToDt_of_wellFormed hwf hdecls hts
  -- Sig amendment 2026-05-03 (Defect 3): broadened premise.
  have hAll : Typed.Decls.AllAppRefToDt tds :=
    AllAppRefToDt_of_wellFormed hwf hdecls hts
  have hinit_inv :
      DrainState.NewFnInputsAppRefToDt tds
        { pending := concretizeSeed tds, seen := {}, mono := {},
          newFunctions := #[], newDataTypes := #[] } :=
    RefClosedBody.DrainState.NewFnInputsAppRefToDt.init tds (concretizeSeed tds)
  have hinit_pargs :
      DrainState.PendingArgsAppRefToDt tds
        { pending := concretizeSeed tds, seen := {}, mono := {},
          newFunctions := #[], newDataTypes := #[] } :=
    RefClosedBody.DrainState.PendingArgsAppRefToDt.init hAll
  exact RefClosedBody.concretize_drain_preserves_NewFnInputsAppRefToDt
    hAll hFnIn _ _ hinit_inv hinit_pargs hdrain

theorem concretize_produces_NewFnOutputAppRefToDt
    {t : Source.Toplevel} {decls : Source.Decls} {tds : Typed.Decls}
    (hwf : WellFormed t)
    (hdecls : t.mkDecls = .ok decls)
    (hts : t.checkAndSimplify = .ok tds)
    {drained : DrainState}
    (hdrain : concretizeDrain tds (concretizeDrainFuel tds)
      { pending := concretizeSeed tds, seen := {}, mono := {},
        newFunctions := #[], newDataTypes := #[] } = .ok drained) :
    drained.NewFnOutputAppRefToDt tds := by
  have hCtor : Typed.Decls.AllCtorArgsAppRefToDt tds :=
    AllCtorArgsAppRefToDt_of_wellFormed hwf hdecls hts
  have hFnOut : Typed.Decls.AllFnOutputAppRefToDt tds :=
    AllFnOutputAppRefToDt_of_wellFormed hwf hdecls hts
  -- Sig amendment 2026-05-03 (Defect 3): broadened premise.
  have hAll : Typed.Decls.AllAppRefToDt tds :=
    AllAppRefToDt_of_wellFormed hwf hdecls hts
  have hinit_inv :
      DrainState.NewFnOutputAppRefToDt tds
        { pending := concretizeSeed tds, seen := {}, mono := {},
          newFunctions := #[], newDataTypes := #[] } :=
    RefClosedBody.DrainState.NewFnOutputAppRefToDt.init tds (concretizeSeed tds)
  have hinit_pargs :
      DrainState.PendingArgsAppRefToDt tds
        { pending := concretizeSeed tds, seen := {}, mono := {},
          newFunctions := #[], newDataTypes := #[] } :=
    RefClosedBody.DrainState.PendingArgsAppRefToDt.init hAll
  exact RefClosedBody.concretize_drain_preserves_NewFnOutputAppRefToDt
    hAll hFnOut _ _ hinit_inv hinit_pargs hdrain

section refClosed_helpers

/-- Per-position extraction from a successful list `mapM`: if
`l.mapM f = .ok r`, then for any index `i < l.length`, `r` has matching
length and `f l[i] = .ok r[i]`. -/
theorem List.mapM_ok_at_index_lemma {α β ε : Type}
    {f : α → Except ε β} :
    ∀ (l : List α) (r : List β),
      l.mapM f = .ok r →
      r.length = l.length ∧
      ∀ (i : Nat) (hi : i < l.length),
        ∃ (hi' : i < r.length), f (l[i]'hi) = .ok (r[i]'hi')
  | [], r, h => by
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨rfl, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  | (x :: xs), r, h => by
    simp only [List.mapM_cons, bind, Except.bind] at h
    split at h
    · cases h
    rename_i fx hfx
    split at h
    · cases h
    rename_i fxs hfxs
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    obtain ⟨hlen, hind⟩ := List.mapM_ok_at_index_lemma xs fxs hfxs
    refine ⟨by simp [hlen], ?_⟩
    intro i hi
    cases i with
    | zero =>
      refine ⟨by simp, ?_⟩
      simp; exact hfx
    | succ k =>
      have hk_lt : k < xs.length := by
        simp at hi; omega
      obtain ⟨hk_lt_fxs, hf_eq⟩ := hind k hk_lt
      refine ⟨by simp; omega, ?_⟩
      simp; exact hf_eq

end refClosed_helpers

/-! ### Per-arm `appsResolved` discharge for the umbrella.

These helpers wrap `concretizeBuild_*_origin` + `AppsReachedCond` post-drain
+ `SeenSubsetMono` to produce the `containsApp ⟶ ∃ mono entry` discharge
needed by `typToConcrete_RefClosed_via_AppRefToDtOrNewDt` at each per-element
site of `Toplevel.concretize_produces_refClosed_entry`. -/

/-- AllAppsP-coverage of a tds-source function's inputs/output via
`AppsReachedCond` post-drain (`pending = ∅`). -/
theorem AppsReachedCond_function_AllAppsP_seen_post_drain
    {tds : Typed.Decls} {drained : DrainState} {name : Global} {f_src : Typed.Function}
    (hARC : drained.AppsReachedCond tds)
    (hPE : ∀ q, q ∈ drained.pending → False)
    (hget : tds.getByKey name = some (.function f_src))
    (hpe : f_src.params = []) :
    (∀ lt ∈ f_src.inputs, Typ.AllAppsP
      (fun g args => (g, args) ∈ drained.seen) lt.snd) ∧
    Typ.AllAppsP (fun g args => (g, args) ∈ drained.seen) f_src.output := by
  obtain ⟨h_tds, _, _⟩ := hARC
  have hpe_b : f_src.params.isEmpty := List.isEmpty_iff.mpr hpe
  have hcond := h_tds name (.function f_src) hget
  simp only at hcond
  obtain ⟨h_in, h_out⟩ := hcond hpe_b
  have lift : ∀ {g args}, ((g, args) ∈ drained.seen ∨ (g, args) ∈ drained.pending) →
      (g, args) ∈ drained.seen :=
    fun ha => ha.elim id (fun hp => absurd hp (hPE _))
  refine ⟨?_, ?_⟩
  · intro lt hlt; exact (h_in lt hlt).weaken (fun g args ha => lift ha)
  · exact h_out.weaken (fun g args ha => lift ha)

/-- AllAppsP-coverage of a drained-newFn's inputs/output via `AppsReachedCond`. -/
theorem AppsReachedCond_newFn_AllAppsP_seen_post_drain
    {tds : Typed.Decls} {drained : DrainState} {f : Typed.Function}
    (hARC : drained.AppsReachedCond tds)
    (hPE : ∀ q, q ∈ drained.pending → False)
    (hmem : f ∈ drained.newFunctions) :
    (∀ lt ∈ f.inputs, Typ.AllAppsP
      (fun g args => (g, args) ∈ drained.seen) lt.snd) ∧
    Typ.AllAppsP (fun g args => (g, args) ∈ drained.seen) f.output := by
  obtain ⟨_, _, h_fn⟩ := hARC
  obtain ⟨h_in, h_out⟩ := h_fn f hmem
  have lift : ∀ {g args}, ((g, args) ∈ drained.seen ∨ (g, args) ∈ drained.pending) →
      (g, args) ∈ drained.seen :=
    fun ha => ha.elim id (fun hp => absurd hp (hPE _))
  refine ⟨?_, ?_⟩
  · intro lt hlt; exact (h_in lt hlt).weaken (fun g args ha => lift ha)
  · exact h_out.weaken (fun g args ha => lift ha)

/-- AllAppsP-coverage of a tds-source dataType's ctor argTypes. -/
theorem AppsReachedCond_dataType_AllAppsP_seen_post_drain
    {tds : Typed.Decls} {drained : DrainState} {name : Global} {dt_src : DataType}
    (hARC : drained.AppsReachedCond tds)
    (hPE : ∀ q, q ∈ drained.pending → False)
    (hget : tds.getByKey name = some (.dataType dt_src))
    (hpe : dt_src.params = []) :
    ∀ c ∈ dt_src.constructors, ∀ ty ∈ c.argTypes,
      Typ.AllAppsP (fun g args => (g, args) ∈ drained.seen) ty := by
  obtain ⟨h_tds, _, _⟩ := hARC
  have hpe_b : dt_src.params.isEmpty := List.isEmpty_iff.mpr hpe
  have hcond := h_tds name (.dataType dt_src) hget
  simp only at hcond
  intro c hc ty hty
  have lift : ∀ {g args}, ((g, args) ∈ drained.seen ∨ (g, args) ∈ drained.pending) →
      (g, args) ∈ drained.seen :=
    fun ha => ha.elim id (fun hp => absurd hp (hPE _))
  exact (hcond hpe_b c hc ty hty).weaken (fun g args ha => lift ha)

/-- AllAppsP-coverage of a drained-newDt's ctor argTypes. -/
theorem AppsReachedCond_newDt_AllAppsP_seen_post_drain
    {tds : Typed.Decls} {drained : DrainState} {dt : DataType}
    (hARC : drained.AppsReachedCond tds)
    (hPE : ∀ q, q ∈ drained.pending → False)
    (hmem : dt ∈ drained.newDataTypes) :
    ∀ c ∈ dt.constructors, ∀ ty ∈ c.argTypes,
      Typ.AllAppsP (fun g args => (g, args) ∈ drained.seen) ty := by
  obtain ⟨_, h_dt, _⟩ := hARC
  intro c hc ty hty
  have lift : ∀ {g args}, ((g, args) ∈ drained.seen ∨ (g, args) ∈ drained.pending) →
      (g, args) ∈ drained.seen :=
    fun ha => ha.elim id (fun hp => absurd hp (hPE _))
  exact (h_dt dt hmem c hc ty hty).weaken (fun g args ha => lift ha)

/-- AllAppsP-coverage of a tds-source ctor's argTypes (via companion dt). -/
theorem AppsReachedCond_constructor_AllAppsP_seen_post_drain
    {tds : Typed.Decls} {drained : DrainState} {name : Global}
    {dt_companion : DataType} {c_src : Constructor}
    (hARC : drained.AppsReachedCond tds)
    (hPE : ∀ q, q ∈ drained.pending → False)
    (hget : tds.getByKey name = some (.constructor dt_companion c_src))
    (hcompanion : ∃ key' dt', tds.getByKey key' = some (.dataType dt') ∧
                  c_src ∈ dt'.constructors ∧ dt'.params.isEmpty) :
    ∀ ty ∈ c_src.argTypes,
      Typ.AllAppsP (fun g args => (g, args) ∈ drained.seen) ty := by
  obtain ⟨h_tds, _, _⟩ := hARC
  have hcond := h_tds name (.constructor dt_companion c_src) hget
  simp only at hcond
  intro ty hty
  have lift : ∀ {g args}, ((g, args) ∈ drained.seen ∨ (g, args) ∈ drained.pending) →
      (g, args) ∈ drained.seen :=
    fun ha => ha.elim id (fun hp => absurd hp (hPE _))
  exact (hcond hcompanion ty hty).weaken (fun g args ha => lift ha)

/-- Per-element apps-not-contained discharge for `md_f` in the umbrella's
function arm. Combines `concretizeBuild_function_origin` with `AppsReachedCond`
post-drain to show: no `.app g args` survives in any `md_f.inputs.snd` or
`md_f.output`, since drain covers all source/newFn `.app`s in `seen` and
rewriteTyp scrubs them to `.ref`. -/
theorem function_arm_no_app_md_f
    {t : Source.Toplevel} {decls : Source.Decls} {tds : Typed.Decls}
    {drained : DrainState} {name : Global} {md_f : Typed.Function}
    (hwf : WellFormed t)
    (hdecls : t.mkDecls = .ok decls)
    (hts : t.checkAndSimplify = .ok tds)
    (hdrain : concretizeDrain tds (concretizeDrainFuel tds)
        { pending := concretizeSeed tds, seen := {}, mono := {},
          newFunctions := #[], newDataTypes := #[] } = .ok drained)
    (hSSM : drained.SeenSubsetMono)
    (hARC : drained.AppsReachedCond tds)
    (hPE : ∀ q, q ∈ drained.pending → False)
    (hmd_get : (concretizeBuild tds drained.mono drained.newFunctions
        drained.newDataTypes).getByKey name = some (.function md_f))
    (hMonoShape : drained.MonoShapeOk tds)
    (hNFFS : drained.NewFnFullShape tds)
    (hUnique : Typed.Decls.ConcretizeUniqueNames tds)
    (hSNN : drained.StrongNewNameShape tds)
    {cd : Concrete.Decls}
    (hconc : tds.concretize = .ok cd)
    (hcd_at_name : ∃ d, cd.getByKey name = some d) :
    (∀ p ∈ md_f.inputs, ∀ g args (mono : MonoMap),
        RefClosedBody.Typ.containsApp g args p.2 →
        ∃ concName, mono[(g, args)]? = some concName) ∧
    (∀ g args (mono : MonoMap), RefClosedBody.Typ.containsApp g args md_f.output →
        ∃ concName, mono[(g, args)]? = some concName) := by
  -- Origin split.
  rcases DirectDagBody.concretizeBuild_function_origin tds drained.mono
      drained.newFunctions drained.newDataTypes hmd_get with
    ⟨src_f, hsrc_get, hsrc_params⟩ | ⟨fn_new, hfn_new_mem, hfn_new_name⟩
  · -- (A) source case (mirroring `h_md_AR_combined` source-case shape extraction).
    have hDtNotKey : ∀ dt' ∈ drained.newDataTypes, dt'.name ≠ name := by
      intro dt' hmem heq
      obtain ⟨g_orig, args, dt_orig, hname_eq', hdt_orig_get, _, _⟩ :=
        hSNN.2 dt' hmem
      have heq' : concretizeName g_orig args = concretizeName name #[] := by
        rw [← hname_eq', heq, concretizeName_empty_args]
      have hKey : ∃ d, cd.getByKey (concretizeName g_orig args) = some d := by
        rw [heq', concretizeName_empty_args]; exact hcd_at_name
      obtain ⟨hg_eq, _⟩ := hUnique hconc g_orig name args #[] heq' hKey
      rw [hg_eq] at hdt_orig_get
      rw [hsrc_get] at hdt_orig_get
      cases (Option.some.inj hdt_orig_get : Typed.Declaration.function src_f = .dataType dt_orig)
    have hCtorNotKey : ∀ dt' ∈ drained.newDataTypes, ∀ c ∈ dt'.constructors,
        dt'.name.pushNamespace c.nameHead ≠ name := by
      intro dt' hmem c hc heq
      let collisionArg : Typ := .ref ⟨.mkSimple c.nameHead⟩
      have hLHS_eq : concretizeName dt'.name #[collisionArg] =
          dt'.name.pushNamespace c.nameHead :=
        RefClosedBody.concretizeName_singleton_ref_simple dt'.name c.nameHead
      have heq_concName :
          concretizeName dt'.name #[collisionArg] = concretizeName name #[] := by
        rw [hLHS_eq, heq, concretizeName_empty_args]
      have hKey : ∃ d, cd.getByKey (concretizeName dt'.name #[collisionArg]) = some d := by
        rw [hLHS_eq, heq]; exact hcd_at_name
      obtain ⟨_, hargs_eq⟩ :=
        hUnique hconc dt'.name name #[collisionArg] #[] heq_concName hKey
      have h0 : (#[collisionArg] : Array Typ).size = 0 := by rw [hargs_eq]; rfl
      have h1 : (#[collisionArg] : Array Typ).size = 1 := rfl
      omega
    -- Get source-side AllAppsP coverage via `AppsReachedCond` + pending-empty.
    have ⟨hCov_in_src, hCov_out_src⟩ :=
      AppsReachedCond_function_AllAppsP_seen_post_drain hARC hPE hsrc_get hsrc_params
    -- Override sub-case: the function might have an override in newFunctions.
    by_cases hOverride : ∃ f' ∈ drained.newFunctions, f'.name = name
    · -- Override sub-case.
      obtain ⟨f', hf'_mem, hf'_name⟩ := hOverride
      obtain ⟨g_orig, args, f_orig, _hin_seen, hf_orig_get, hsz, hf'_shape⟩ :=
        hNFFS f' hf'_mem
      have hf'_name' : f'.name = concretizeName g_orig args := by rw [hf'_shape]
      have heq' : concretizeName g_orig args = concretizeName name #[] := by
        rw [← hf'_name', hf'_name, concretizeName_empty_args]
      have hKey : ∃ d, cd.getByKey (concretizeName g_orig args) = some d := by
        rw [heq', concretizeName_empty_args]; exact hcd_at_name
      obtain ⟨hg_eq, hargs_eq⟩ :=
        hUnique hconc g_orig name args #[] heq' hKey
      rw [hg_eq] at hf_orig_get
      rw [hsrc_get] at hf_orig_get
      have hf_orig_eq : f_orig = src_f := by
        have h1 : Typed.Declaration.function src_f = .function f_orig :=
          Option.some.inj hf_orig_get
        injection h1.symm
      have hsubst_empty : mkParamSubst f_orig.params args = fun _ => none := by
        rw [hf_orig_eq, hsrc_params, hargs_eq]
        funext g; simp [mkParamSubst]
      have hOtherFnNotKey : ∀ f'' ∈ drained.newFunctions, f'' ≠ f' →
          f''.name ≠ f'.name := by
        intro f'' hf''_mem hne heq2
        obtain ⟨g2, args2, f_orig2, _, hf_orig2_get, _, hf''_shape⟩ :=
          hNFFS f'' hf''_mem
        obtain ⟨g1, args1, f_orig1, _, hf_orig1_get, _, hf'_shape'⟩ :=
          hNFFS f' hf'_mem
        have hname_f'' : f''.name = concretizeName g2 args2 := by rw [hf''_shape]
        have hname_f' : f'.name = concretizeName g1 args1 := by rw [hf'_shape']
        have heq1 : concretizeName g2 args2 = concretizeName g1 args1 := by
          rw [← hname_f'', heq2, hname_f']
        have hKey1 : ∃ d, cd.getByKey (concretizeName g2 args2) = some d := by
          rw [heq1, ← hname_f', hf'_name]; exact hcd_at_name
        obtain ⟨hg_eq', hargs_eq'⟩ :=
          hUnique hconc g2 g1 args2 args1 heq1 hKey1
        rw [hg_eq'] at hf_orig2_get
        rw [hf_orig1_get] at hf_orig2_get
        have hf_orig_eq' : f_orig2 = f_orig1 := by
          have h1 : Typed.Declaration.function f_orig1 =
              .function f_orig2 := Option.some.inj hf_orig2_get
          injection h1.symm
        apply hne
        rw [hf''_shape, hf'_shape', hg_eq', hargs_eq', hf_orig_eq']
      obtain ⟨md_f_at, hmd_at_get_fn, _hName_fn, hInputs_fn, hOutput_fn, _hBody_fn⟩ :=
        PhaseA2.concretizeBuild_at_newFn_name_full_explicit tds drained.mono
          drained.newFunctions drained.newDataTypes hf'_mem hOtherFnNotKey
      rw [hf'_name] at hmd_at_get_fn
      rw [hmd_at_get_fn] at hmd_get
      have hmd_eq : md_f_at = md_f := by
        have h1 : Typed.Declaration.function md_f_at = .function md_f :=
          Option.some.inj hmd_get
        injection h1
      rw [hmd_eq] at hInputs_fn hOutput_fn
      -- f' is a derived shape; f'.inputs/output collapse to src_f via empty subst.
      have hf'_inputs_proj : f'.inputs = f_orig.inputs.map fun (l, t) =>
          (l, Typ.instantiate (mkParamSubst f_orig.params args) t) := by
        rw [hf'_shape]
      have hf'_output_proj : f'.output =
          Typ.instantiate (mkParamSubst f_orig.params args) f_orig.output := by
        rw [hf'_shape]
      have hf'_inputs_id : f'.inputs = src_f.inputs := by
        rw [hf'_inputs_proj, hsubst_empty, hf_orig_eq]
        induction src_f.inputs with
        | nil => rfl
        | cons hd tl ih =>
          cases hd with
          | mk l t =>
            show (l, Typ.instantiate (fun _ => none) t) ::
                tl.map (fun (lt : Local × Typ) =>
                  (lt.1, Typ.instantiate (fun _ => none) lt.2)) =
              (l, t) :: tl
            rw [Typ.instantiate_empty_id, ih]
      have hf'_output_eq : f'.output = src_f.output := by
        rw [hf'_output_proj, hsubst_empty, hf_orig_eq, Typ.instantiate_empty_id]
      rw [hf'_inputs_id] at hInputs_fn
      rw [hf'_output_eq] at hOutput_fn
      -- Now md_f.inputs = src_f.inputs.map fun (l,t) => (l, rewriteTyp ∅ mono t),
      -- md_f.output = rewriteTyp ∅ mono src_f.output.
      refine ⟨?_, ?_⟩
      · intro p hp_mem
        rw [hInputs_fn] at hp_mem
        obtain ⟨src_lt, hsrc_lt_mem, hp_eq⟩ := List.mem_map.mp hp_mem
        rw [← hp_eq]
        intro g args mono hcontain
        exact RefClosedBody.appsResolved_via_seen_coverage_rewrite
          hSSM (hCov_in_src src_lt hsrc_lt_mem) mono g args hcontain
      · rw [hOutput_fn]
        intro g args mono
        exact RefClosedBody.appsResolved_via_seen_coverage_rewrite hSSM hCov_out_src mono g args
    · -- No-override sub-case: standard source path.
      have hFnNotKey : ∀ f' ∈ drained.newFunctions, f'.name ≠ name := by
        intro f' hf'_mem hf'_name
        exact hOverride ⟨f', hf'_mem, hf'_name⟩
      have hexplicit :=
        PhaseA2.concretizeBuild_at_typed_function_explicit tds drained.mono
          drained.newFunctions drained.newDataTypes hsrc_get hsrc_params
          hDtNotKey hFnNotKey hCtorNotKey
      rw [hexplicit] at hmd_get
      let monoF : Typed.Function :=
        { src_f with
          inputs := src_f.inputs.map fun (l, t) =>
            (l, rewriteTyp (fun _ => none) drained.mono t),
          output := rewriteTyp (fun _ => none) drained.mono src_f.output,
          body := rewriteTypedTerm tds (fun _ => none) drained.mono src_f.body }
      have hmd_f_eq : md_f = monoF := by
        have h1 : Typed.Declaration.function monoF = .function md_f :=
          Option.some.inj hmd_get
        have h2 : monoF = md_f := by injection h1
        exact h2.symm
      refine ⟨?_, ?_⟩
      · intro p hp_mem
        rw [hmd_f_eq] at hp_mem
        change p ∈ src_f.inputs.map (fun lt => (lt.1, rewriteTyp _ drained.mono lt.snd))
          at hp_mem
        obtain ⟨src_lt, hsrc_lt_mem, hp_eq⟩ := List.mem_map.mp hp_mem
        rw [← hp_eq]
        intro g args mono hcontain
        exact RefClosedBody.appsResolved_via_seen_coverage_rewrite
          hSSM (hCov_in_src src_lt hsrc_lt_mem) mono g args hcontain
      · rw [hmd_f_eq]
        change ∀ g args (mono : MonoMap),
          RefClosedBody.Typ.containsApp g args
            (rewriteTyp _ drained.mono src_f.output) → _
        intro g args mono
        exact RefClosedBody.appsResolved_via_seen_coverage_rewrite hSSM hCov_out_src mono g args
  · -- (B) newFn case: md_f comes from rewriting fn_new.
    rw [← hfn_new_name] at hmd_get
    have hcd_at_fn : ∃ d, cd.getByKey fn_new.name = some d := by
      rw [hfn_new_name]; exact hcd_at_name
    have hOtherFnNotKey : ∀ f' ∈ drained.newFunctions, f' ≠ fn_new →
        f'.name ≠ fn_new.name := by
      intro f' hf'_mem hne heq
      obtain ⟨g_orig, args, f_orig, _, hf_get, _, hshape⟩ :=
        hNFFS f' hf'_mem
      obtain ⟨g_new_orig, args_new, fn_new_orig, _, hf_new_get, _, hshape_new⟩ :=
        hNFFS fn_new hfn_new_mem
      have hname_f' : f'.name = concretizeName g_orig args := by rw [hshape]
      have hname_fn : fn_new.name = concretizeName g_new_orig args_new := by rw [hshape_new]
      have heq1 : concretizeName g_orig args =
          concretizeName g_new_orig args_new := by
        rw [← hname_f', heq, hname_fn]
      have hKey1 : ∃ d, cd.getByKey (concretizeName g_orig args) = some d := by
        rw [heq1, ← hname_fn]; exact hcd_at_fn
      obtain ⟨hg_eq, hargs_eq⟩ :=
        hUnique hconc g_orig g_new_orig args args_new heq1 hKey1
      rw [hg_eq] at hf_get
      rw [hf_new_get] at hf_get
      have hf_orig_eq : f_orig = fn_new_orig := by
        have h1 : Typed.Declaration.function fn_new_orig =
            .function f_orig := Option.some.inj hf_get
        injection h1.symm
      apply hne
      rw [hshape, hshape_new, hg_eq, hargs_eq, hf_orig_eq]
    obtain ⟨md_f_at, hmd_at_get_fn, _hName_fn, hInputs_fn, hOutput_fn, _hBody_fn⟩ :=
      PhaseA2.concretizeBuild_at_newFn_name_full_explicit tds drained.mono
        drained.newFunctions drained.newDataTypes hfn_new_mem hOtherFnNotKey
    rw [hmd_at_get_fn] at hmd_get
    have hmd_eq : md_f_at = md_f := by
      have h1 : Typed.Declaration.function md_f_at = .function md_f :=
        Option.some.inj hmd_get
      injection h1
    rw [hmd_eq] at hInputs_fn hOutput_fn
    -- AppsReachedCond newFn clause gives AllAppsP for fn_new.inputs/output.
    have ⟨hCov_in_new, hCov_out_new⟩ :=
      AppsReachedCond_newFn_AllAppsP_seen_post_drain hARC hPE hfn_new_mem
    refine ⟨?_, ?_⟩
    · intro p hp_mem
      rw [hInputs_fn] at hp_mem
      obtain ⟨lt0, hlt0_mem, hp_eq⟩ := List.mem_map.mp hp_mem
      rw [← hp_eq]
      intro g args mono hcontain
      exact RefClosedBody.appsResolved_via_seen_coverage_rewrite
        hSSM (hCov_in_new lt0 hlt0_mem) mono g args hcontain
    · rw [hOutput_fn]
      intro g args mono
      exact RefClosedBody.appsResolved_via_seen_coverage_rewrite hSSM hCov_out_new mono g args

/-- DataType arm version: per-element apps-not-contained discharge for
`md_dt.constructors[i].argTypes` items. -/
theorem dataType_arm_no_app_md_dt
    {t : Source.Toplevel} {decls : Source.Decls} {tds : Typed.Decls}
    {drained : DrainState} {name : Global} {md_dt : DataType}
    (hwf : WellFormed t)
    (hdecls : t.mkDecls = .ok decls)
    (hts : t.checkAndSimplify = .ok tds)
    (hdrain : concretizeDrain tds (concretizeDrainFuel tds)
        { pending := concretizeSeed tds, seen := {}, mono := {},
          newFunctions := #[], newDataTypes := #[] } = .ok drained)
    (hSSM : drained.SeenSubsetMono)
    (hARC : drained.AppsReachedCond tds)
    (hPE : ∀ q, q ∈ drained.pending → False)
    (hmd_get : (concretizeBuild tds drained.mono drained.newFunctions
        drained.newDataTypes).getByKey name = some (.dataType md_dt))
    (hMonoShape : drained.MonoShapeOk tds)
    (hNDFS : drained.NewDtFullShape tds)
    (hUnique : Typed.Decls.ConcretizeUniqueNames tds)
    (hSNN : drained.StrongNewNameShape tds)
    {cd : Concrete.Decls}
    (hconc : tds.concretize = .ok cd)
    (hcd_at_name : ∃ d, cd.getByKey name = some d) :
    ∀ md_c ∈ md_dt.constructors, ∀ t' ∈ md_c.argTypes,
      ∀ g args (mono : MonoMap),
        RefClosedBody.Typ.containsApp g args t' →
        ∃ concName, mono[(g, args)]? = some concName := by
  rcases DirectDagBody.concretizeBuild_dataType_origin tds drained.mono
      drained.newFunctions drained.newDataTypes hmd_get with
    ⟨src_dt, hsrc_get, hsrc_params⟩ | ⟨dt_new, hdt_new_mem, hdt_new_name⟩
  · -- (A) source case.
    have hFnNotKey : ∀ f ∈ drained.newFunctions, f.name ≠ name := by
      intro f hmem heq
      obtain ⟨g_orig, args, f_orig, hname_eq', hf_get, _⟩ := hSNN.1 f hmem
      have heq' : concretizeName g_orig args = concretizeName name #[] := by
        rw [← hname_eq', heq, concretizeName_empty_args]
      have hKey : ∃ d, cd.getByKey (concretizeName g_orig args) = some d := by
        rw [heq', concretizeName_empty_args]; exact hcd_at_name
      obtain ⟨hg_eq, _⟩ := hUnique hconc g_orig name args #[] heq' hKey
      rw [hg_eq] at hf_get
      rw [hsrc_get] at hf_get
      cases hf_get
    have hCtorNotKey : ∀ dt' ∈ drained.newDataTypes, ∀ c ∈ dt'.constructors,
        dt'.name.pushNamespace c.nameHead ≠ name := by
      intro dt' hmem c hc heq
      let collisionArg : Typ := .ref ⟨.mkSimple c.nameHead⟩
      have hLHS_eq : concretizeName dt'.name #[collisionArg] =
          dt'.name.pushNamespace c.nameHead :=
        RefClosedBody.concretizeName_singleton_ref_simple dt'.name c.nameHead
      have heq_concName :
          concretizeName dt'.name #[collisionArg] = concretizeName name #[] := by
        rw [hLHS_eq, heq, concretizeName_empty_args]
      have hKey : ∃ d, cd.getByKey (concretizeName dt'.name #[collisionArg]) = some d := by
        rw [hLHS_eq, heq]; exact hcd_at_name
      obtain ⟨_, hargs_eq⟩ :=
        hUnique hconc dt'.name name #[collisionArg] #[] heq_concName hKey
      have h0 : (#[collisionArg] : Array Typ).size = 0 := by rw [hargs_eq]; rfl
      have h1 : (#[collisionArg] : Array Typ).size = 1 := rfl
      omega
    have hCov_src :=
      AppsReachedCond_dataType_AllAppsP_seen_post_drain hARC hPE hsrc_get hsrc_params
    -- md_dt.constructors = rewrittenCtors via override or no-override.
    let rewrittenCtors : List Constructor := src_dt.constructors.map fun c =>
      { c with argTypes := c.argTypes.map (rewriteTyp (fun _ => none) drained.mono) }
    have hmd_dt_ctors : md_dt.constructors = rewrittenCtors := by
      by_cases hOverride : ∃ dt' ∈ drained.newDataTypes, dt'.name = name
      · obtain ⟨dt', hdt'_mem, hdt'_name⟩ := hOverride
        obtain ⟨g_orig, args, dt_orig, _hin_seen, hdt_orig_get, hsz, hdt'_shape⟩ :=
          hNDFS dt' hdt'_mem
        have hdt'_name' : dt'.name = concretizeName g_orig args := by rw [hdt'_shape]
        have heq' : concretizeName g_orig args = concretizeName name #[] := by
          rw [← hdt'_name', hdt'_name, concretizeName_empty_args]
        have hKey : ∃ d, cd.getByKey (concretizeName g_orig args) = some d := by
          rw [heq', concretizeName_empty_args]; exact hcd_at_name
        obtain ⟨hg_eq, hargs_eq⟩ :=
          hUnique hconc g_orig name args #[] heq' hKey
        rw [hg_eq] at hdt_orig_get
        rw [hsrc_get] at hdt_orig_get
        have hdt_orig_eq : dt_orig = src_dt := by
          have h1 : Typed.Declaration.dataType src_dt = .dataType dt_orig :=
            Option.some.inj hdt_orig_get
          injection h1.symm
        have hsubst_empty : mkParamSubst dt_orig.params args = fun _ => none := by
          rw [hdt_orig_eq, hsrc_params, hargs_eq]
          funext g; simp [mkParamSubst]
        have hOtherDtNotKey : ∀ dt'' ∈ drained.newDataTypes, dt'' ≠ dt' →
            dt''.name ≠ dt'.name := by
          intro dt'' hdt''_mem hne heq2
          obtain ⟨g2, args2, dt_orig2, _, hdt_orig2_get, _, hdt''_shape⟩ :=
            hNDFS dt'' hdt''_mem
          obtain ⟨g1, args1, dt_orig1, _, hdt_orig1_get, _, hdt'_shape'⟩ :=
            hNDFS dt' hdt'_mem
          have hname_dt'' : dt''.name = concretizeName g2 args2 := by rw [hdt''_shape]
          have hname_dt' : dt'.name = concretizeName g1 args1 := by rw [hdt'_shape']
          have heq1 : concretizeName g2 args2 = concretizeName g1 args1 := by
            rw [← hname_dt'', heq2, hname_dt']
          have hKey1 : ∃ d, cd.getByKey (concretizeName g2 args2) = some d := by
            rw [heq1, ← hname_dt', hdt'_name]; exact hcd_at_name
          obtain ⟨hg_eq', hargs_eq'⟩ :=
            hUnique hconc g2 g1 args2 args1 heq1 hKey1
          rw [hg_eq'] at hdt_orig2_get
          rw [hdt_orig1_get] at hdt_orig2_get
          have hdt_orig_eq' : dt_orig2 = dt_orig1 := by
            have h1 : Typed.Declaration.dataType dt_orig1 =
                .dataType dt_orig2 := Option.some.inj hdt_orig2_get
            injection h1.symm
          apply hne
          rw [hdt''_shape, hdt'_shape', hg_eq', hargs_eq', hdt_orig_eq']
        have hDtCtorNotKey : ∀ dt'' ∈ drained.newDataTypes, ∀ c ∈ dt''.constructors,
            dt''.name.pushNamespace c.nameHead ≠ dt'.name := by
          intro dt'' hdt''_mem c hc heq2
          rw [hdt'_name] at heq2
          exact hCtorNotKey dt'' hdt''_mem c hc heq2
        have hFnNotKey' : ∀ f ∈ drained.newFunctions, f.name ≠ dt'.name := by
          intro f hf_mem hfeq
          rw [hdt'_name] at hfeq
          exact hFnNotKey f hf_mem hfeq
        obtain ⟨md_dt_at, hmd_at_get_dt, _hName_dt, _hParams_dt, hCtors_dt⟩ :=
          PhaseA2.concretizeBuild_at_newDt_name_full_explicit tds drained.mono
            drained.newFunctions drained.newDataTypes hdt'_mem
            hDtCtorNotKey hFnNotKey' hOtherDtNotKey
        rw [hdt'_name] at hmd_at_get_dt
        rw [hmd_at_get_dt] at hmd_get
        have hmd_eq : md_dt_at = md_dt := by
          have h1 : Typed.Declaration.dataType md_dt_at = .dataType md_dt :=
            Option.some.inj hmd_get
          injection h1
        rw [hmd_eq] at hCtors_dt
        have hdt'_ctors_proj : dt'.constructors =
            dt_orig.constructors.map (fun c =>
              ({ c with argTypes :=
                c.argTypes.map (Typ.instantiate (mkParamSubst dt_orig.params args)) }
                : Constructor)) := by
          rw [hdt'_shape]
        have hdt'_ctors_id : dt'.constructors = src_dt.constructors := by
          rw [hdt'_ctors_proj, hsubst_empty, hdt_orig_eq]
          induction src_dt.constructors with
          | nil => rfl
          | cons hd tl ih =>
            have hat_eq : hd.argTypes.map (Typ.instantiate (fun _ => none))
                = hd.argTypes := by
              induction hd.argTypes with
              | nil => rfl
              | cons hd' tl' ih' =>
                show Typ.instantiate (fun _ => none) hd' :: tl'.map _ = hd' :: tl'
                rw [Typ.instantiate_empty_id, ih']
            show ({ hd with argTypes :=
                    hd.argTypes.map (Typ.instantiate (fun _ => none)) } : Constructor)
                :: tl.map _ = hd :: tl
            rw [hat_eq, ih]
        show md_dt.constructors = rewrittenCtors
        rw [hCtors_dt, hdt'_ctors_id]
      · have hDtNotKey : ∀ dt' ∈ drained.newDataTypes, dt'.name ≠ name := by
          intro dt' hmem heq2
          exact hOverride ⟨dt', hmem, heq2⟩
        have hexplicit :=
          PhaseA2.concretizeBuild_at_typed_dataType_explicit tds drained.mono
            drained.newFunctions drained.newDataTypes hsrc_get hsrc_params
            hDtNotKey hFnNotKey hCtorNotKey
        rw [hexplicit] at hmd_get
        have h1 : Typed.Declaration.dataType
          ({ src_dt with constructors := rewrittenCtors } : DataType) =
          .dataType md_dt := Option.some.inj hmd_get
        have h2 : md_dt = ({ src_dt with constructors := rewrittenCtors } : DataType) := by
          have h3 : ({ src_dt with constructors := rewrittenCtors } : DataType) = md_dt := by
            injection h1
          exact h3.symm
        rw [h2]
    intro md_c hmd_c_mem t' ht'_mem g args mono hcontain
    rw [hmd_dt_ctors] at hmd_c_mem
    obtain ⟨src_c, hsrc_c_mem, hmd_c_eq⟩ := List.mem_map.mp hmd_c_mem
    rw [← hmd_c_eq] at ht'_mem
    -- ht'_mem : t' ∈ src_c.argTypes.map (rewriteTyp ∅ drained.mono)
    obtain ⟨src_t, hsrc_t_mem, ht'_eq⟩ := List.mem_map.mp ht'_mem
    have hCov_src_t : Typ.AllAppsP (fun g args => (g, args) ∈ drained.seen) src_t :=
      hCov_src src_c hsrc_c_mem src_t hsrc_t_mem
    rw [← ht'_eq] at hcontain
    exact RefClosedBody.appsResolved_via_seen_coverage_rewrite
      hSSM hCov_src_t mono g args hcontain
  · -- (B) newDt case.
    rw [← hdt_new_name] at hmd_get
    have hcd_at_dt_new : ∃ d, cd.getByKey dt_new.name = some d := by
      rw [hdt_new_name]; exact hcd_at_name
    have hOtherDtNotKey : ∀ dt' ∈ drained.newDataTypes, dt' ≠ dt_new →
        dt'.name ≠ dt_new.name := by
      intro dt' hmem hne heq
      obtain ⟨g_orig, args, dt_orig, _, hdt_get, _, hshape⟩ := hNDFS dt' hmem
      obtain ⟨g_new_orig, args_new, dt_new_orig, _, hdt_new_get, _, hshape_new⟩ :=
        hNDFS dt_new hdt_new_mem
      have hname_dt' : dt'.name = concretizeName g_orig args := by rw [hshape]
      have hname_dt_new : dt_new.name = concretizeName g_new_orig args_new := by rw [hshape_new]
      have heq1 : concretizeName g_orig args =
          concretizeName g_new_orig args_new := by
        rw [← hname_dt', heq, hname_dt_new]
      have hKey1 : ∃ d, cd.getByKey (concretizeName g_orig args) = some d := by
        rw [heq1, ← hname_dt_new]; exact hcd_at_dt_new
      obtain ⟨hg_eq, hargs_eq⟩ :=
        hUnique hconc g_orig g_new_orig args args_new heq1 hKey1
      rw [hg_eq] at hdt_get
      rw [hdt_new_get] at hdt_get
      have hdt_orig_eq : dt_orig = dt_new_orig := by
        have h1 : Typed.Declaration.dataType dt_new_orig =
            .dataType dt_orig := Option.some.inj hdt_get
        injection h1.symm
      apply hne
      rw [hshape, hshape_new, hg_eq, hargs_eq, hdt_orig_eq]
    have hDtCtorNotKey : ∀ dt' ∈ drained.newDataTypes, ∀ c ∈ dt'.constructors,
        dt'.name.pushNamespace c.nameHead ≠ dt_new.name := by
      intro dt' hdt'_mem c hc heq
      let collisionArg : Typ := .ref ⟨.mkSimple c.nameHead⟩
      have hLHS_eq : concretizeName dt'.name #[collisionArg] =
          dt'.name.pushNamespace c.nameHead :=
        RefClosedBody.concretizeName_singleton_ref_simple dt'.name c.nameHead
      obtain ⟨g_orig, args, dt_orig, hname_eq', hdt_orig_get, hsz', _⟩ :=
        hSNN.2 dt' hdt'_mem
      obtain ⟨g_new_orig, args_new, dt_new_orig, hname_eq_new, hdt_new_get,
              hsz_new, _⟩ := hSNN.2 dt_new hdt_new_mem
      have heq_concName : concretizeName dt'.name #[collisionArg] =
          concretizeName g_new_orig args_new := by
        rw [hLHS_eq, heq, hname_eq_new]
      have hKey1 : ∃ d, cd.getByKey
          (concretizeName dt'.name #[collisionArg]) = some d := by
        rw [hLHS_eq, heq]; exact hcd_at_dt_new
      obtain ⟨hname_dt'_eq, hargs_witness⟩ :=
        hUnique hconc dt'.name g_new_orig #[collisionArg] args_new heq_concName hKey1
      have hsz_args : args_new.size = 1 := by rw [← hargs_witness]; rfl
      obtain ⟨g'_orig, args'_dt, dt'_orig, hdt'_name, hdt'_get, hdt'_sz, _⟩ :=
        hSNN.2 dt' hdt'_mem
      have heq2 : concretizeName g'_orig args'_dt = concretizeName g_new_orig #[] := by
        rw [← hdt'_name, hname_dt'_eq, concretizeName_empty_args]
      have hconc_fold : (concretizeBuild tds drained.mono drained.newFunctions
            drained.newDataTypes).foldlM (init := default) step4Lower = .ok cd := by
        have hconc_eq := hconc
        unfold Typed.Decls.concretize at hconc_eq
        simp only [bind, Except.bind] at hconc_eq
        rw [hdrain] at hconc_eq
        exact hconc_eq
      have hKey2 : ∃ d, cd.getByKey (concretizeName g'_orig args'_dt) = some d := by
        rw [← hdt'_name]
        exact RefClosedBody.cd_has_some_at_newDt_name hconc_fold hdt'_mem
      obtain ⟨_hg'_eq, hargs'_eq⟩ :=
        hUnique hconc g'_orig g_new_orig args'_dt #[] heq2 hKey2
      have hargs'_size : args'_dt.size = 0 := by rw [hargs'_eq]; rfl
      rw [hargs'_size] at hdt'_sz
      rw [_hg'_eq, hdt_new_get] at hdt'_get
      have hdt_orig_eq : dt'_orig = dt_new_orig := by
        have h1 : (Typed.Declaration.dataType dt_new_orig) =
            .dataType dt'_orig := Option.some.inj hdt'_get
        injection h1.symm
      rw [hdt_orig_eq] at hdt'_sz
      rw [hsz_args] at hsz_new
      omega
    have hFnNotKey' : ∀ f ∈ drained.newFunctions, f.name ≠ dt_new.name := by
      intro f hmem heq2
      obtain ⟨g_orig, args, f_orig, hname_eq', hf_get, _⟩ := hSNN.1 f hmem
      obtain ⟨g_new_orig, args_new, dt_new_orig, hname_eq_new, hdt_new_get, _, _⟩ :=
        hSNN.2 dt_new hdt_new_mem
      have heq1 : concretizeName g_orig args = concretizeName g_new_orig args_new := by
        rw [← hname_eq', heq2, hname_eq_new]
      have hKey1 : ∃ d, cd.getByKey (concretizeName g_orig args) = some d := by
        rw [heq1, ← hname_eq_new]; exact hcd_at_dt_new
      obtain ⟨hg_eq, _⟩ := hUnique hconc g_orig g_new_orig args args_new heq1 hKey1
      rw [hg_eq] at hf_get
      rw [hdt_new_get] at hf_get
      cases hf_get
    obtain ⟨md_dt_at, hmd_at_get_dt, _hName_dt, _hParams_dt, hCtors_dt⟩ :=
      PhaseA2.concretizeBuild_at_newDt_name_full_explicit tds drained.mono
        drained.newFunctions drained.newDataTypes hdt_new_mem
        hDtCtorNotKey hFnNotKey' hOtherDtNotKey
    rw [hmd_at_get_dt] at hmd_get
    have hmd_eq : md_dt_at = md_dt := by
      have h1 : Typed.Declaration.dataType md_dt_at = .dataType md_dt :=
        Option.some.inj hmd_get
      injection h1
    rw [hmd_eq] at hCtors_dt
    -- AppsReachedCond newDt clause gives AllAppsP for dt_new.
    have hCov_new := AppsReachedCond_newDt_AllAppsP_seen_post_drain hARC hPE hdt_new_mem
    intro md_c hmd_c_mem t' ht'_mem g args mono hcontain
    -- md_c ∈ md_dt.constructors → via hCtors_dt, md_c is some dt_new.constructors[i]'s rewrite.
    rw [hCtors_dt] at hmd_c_mem
    obtain ⟨src_c, hsrc_c_mem, hmd_c_eq⟩ := List.mem_map.mp hmd_c_mem
    rw [← hmd_c_eq] at ht'_mem
    obtain ⟨src_t, hsrc_t_mem, ht'_eq⟩ := List.mem_map.mp ht'_mem
    have hCov_src_t : Typ.AllAppsP (fun g args => (g, args) ∈ drained.seen) src_t :=
      hCov_new src_c hsrc_c_mem src_t hsrc_t_mem
    rw [← ht'_eq] at hcontain
    exact RefClosedBody.appsResolved_via_seen_coverage_rewrite
      hSSM hCov_src_t mono g args hcontain

/-- Constructor arm version: per-element apps-not-contained discharge for
`md_c.argTypes`. -/
theorem constructor_arm_no_app_md_c
    {t : Source.Toplevel} {decls : Source.Decls} {tds : Typed.Decls}
    {drained : DrainState} {name : Global} {md_dt : DataType} {md_c : Constructor}
    (hwf : WellFormed t)
    (hdecls : t.mkDecls = .ok decls)
    (hts : t.checkAndSimplify = .ok tds)
    (hdrain : concretizeDrain tds (concretizeDrainFuel tds)
        { pending := concretizeSeed tds, seen := {}, mono := {},
          newFunctions := #[], newDataTypes := #[] } = .ok drained)
    (hSSM : drained.SeenSubsetMono)
    (hARC : drained.AppsReachedCond tds)
    (hPE : ∀ q, q ∈ drained.pending → False)
    (hmd_get : (concretizeBuild tds drained.mono drained.newFunctions
        drained.newDataTypes).getByKey name = some (.constructor md_dt md_c))
    (hMonoShape : drained.MonoShapeOk tds)
    (hNDFS : drained.NewDtFullShape tds)
    (hUnique : Typed.Decls.ConcretizeUniqueNames tds)
    (hSNN : drained.StrongNewNameShape tds)
    {cd : Concrete.Decls}
    (hconc : tds.concretize = .ok cd)
    (hcd_at_name : ∃ d, cd.getByKey name = some d) :
    ∀ t' ∈ md_c.argTypes,
      ∀ g args (mono : MonoMap),
        RefClosedBody.Typ.containsApp g args t' →
        ∃ concName, mono[(g, args)]? = some concName := by
  rcases PhaseA2.concretizeBuild_ctor_origin tds drained.mono drained.newFunctions
      drained.newDataTypes hmd_get with
    ⟨src_dt, src_c, hsrc_get, hsrc_params⟩ |
      ⟨dt_new, hdt_new_mem, c_new, hc_new_mem, hpush_eq⟩
  · -- (A) source case: tds .ctor at name with src_dt.params = [].
    -- Companion via mkDecls_ctor_companion + checkAndSimplify_src_dt_to_td.
    have hP_fn := FnMatchP_checkAndSimplify hdecls hts
    have hsrc_ctor : decls.getByKey name = some (.constructor src_dt src_c) :=
      (hP_fn name).2.2 src_dt src_c hsrc_get
    obtain ⟨hsrc_dt, hcmem⟩ := mkDecls_ctor_companion hdecls name src_dt src_c hsrc_ctor
    obtain ⟨src_dt_td, htd_dt⟩ := checkAndSimplify_src_dt_to_td hdecls hts hsrc_dt
    have hP := TdDtParamsMatchP_checkAndSimplify hdecls hts
    have hsrc_again : decls.getByKey src_dt.name = some (.dataType src_dt_td) :=
      hP src_dt.name src_dt_td htd_dt
    have hdt_eq : src_dt = src_dt_td := by
      rw [hsrc_dt] at hsrc_again
      cases hsrc_again; rfl
    have hcompanion : ∃ key' dt', tds.getByKey key' = some (.dataType dt') ∧
        src_c ∈ dt'.constructors ∧ dt'.params.isEmpty := by
      refine ⟨src_dt.name, src_dt_td, hdt_eq ▸ htd_dt, hdt_eq ▸ hcmem, ?_⟩
      rw [← hdt_eq]; exact List.isEmpty_iff.mpr hsrc_params
    have hCov_src := AppsReachedCond_constructor_AllAppsP_seen_post_drain hARC hPE
      hsrc_get hcompanion
    -- Now md_c.argTypes = src_c.argTypes.map (rewriteTyp ∅ drained.mono).
    -- Path: concretizeBuild_at_typed_ctor_explicit gives this shape.
    have hcd_at_name' := hcd_at_name
    have hDtNotKey : ∀ dt' ∈ drained.newDataTypes, dt'.name ≠ name := by
      intro dt' hmem heq
      obtain ⟨g_orig, args, dt_orig, hname_eq', hdt_orig_get, _, _⟩ := hSNN.2 dt' hmem
      have heq' : concretizeName g_orig args = concretizeName name #[] := by
        rw [← hname_eq', heq, concretizeName_empty_args]
      have hKey : ∃ d, cd.getByKey (concretizeName g_orig args) = some d := by
        rw [heq', concretizeName_empty_args]; exact hcd_at_name
      obtain ⟨hg_eq, _⟩ := hUnique hconc g_orig name args #[] heq' hKey
      rw [hg_eq] at hdt_orig_get
      rw [hsrc_get] at hdt_orig_get; cases hdt_orig_get
    have hFnNotKey : ∀ f ∈ drained.newFunctions, f.name ≠ name := by
      intro f hmem heq
      obtain ⟨g_orig, args, f_orig, hname_eq', hf_get, _⟩ := hSNN.1 f hmem
      have heq' : concretizeName g_orig args = concretizeName name #[] := by
        rw [← hname_eq', heq, concretizeName_empty_args]
      have hKey : ∃ d, cd.getByKey (concretizeName g_orig args) = some d := by
        rw [heq', concretizeName_empty_args]; exact hcd_at_name
      obtain ⟨hg_eq, _⟩ := hUnique hconc g_orig name args #[] heq' hKey
      rw [hg_eq] at hf_get
      rw [hsrc_get] at hf_get; cases hf_get
    have hCtorNotKey : ∀ dt' ∈ drained.newDataTypes, ∀ c ∈ dt'.constructors,
        dt'.name.pushNamespace c.nameHead ≠ name := by
      intro dt' hmem c hc heq
      let collisionArg : Typ := .ref ⟨.mkSimple c.nameHead⟩
      have hLHS_eq : concretizeName dt'.name #[collisionArg] =
          dt'.name.pushNamespace c.nameHead :=
        RefClosedBody.concretizeName_singleton_ref_simple dt'.name c.nameHead
      have heq_concName :
          concretizeName dt'.name #[collisionArg] = concretizeName name #[] := by
        rw [hLHS_eq, heq, concretizeName_empty_args]
      have hKey : ∃ d, cd.getByKey (concretizeName dt'.name #[collisionArg]) = some d := by
        rw [hLHS_eq, heq]; exact hcd_at_name
      obtain ⟨_, hargs_eq⟩ :=
        hUnique hconc dt'.name name #[collisionArg] #[] heq_concName hKey
      have h0 : (#[collisionArg] : Array Typ).size = 0 := by rw [hargs_eq]; rfl
      have h1 : (#[collisionArg] : Array Typ).size = 1 := rfl
      omega
    have hexplicit :=
      PhaseA2.concretizeBuild_at_typed_ctor_explicit tds drained.mono
        drained.newFunctions drained.newDataTypes hsrc_get hsrc_params
        hDtNotKey hFnNotKey hCtorNotKey
    -- hexplicit : (...).getByKey name = some (.constructor newDt newCtor)
    -- where newCtor.argTypes = src_c.argTypes.map (rewriteTyp ∅ drained.mono).
    rw [hexplicit] at hmd_get
    -- Extract md_c equality.
    let newArgs : List Typ := src_c.argTypes.map (fun t => rewriteTyp (fun _ => none) drained.mono t)
    let newCtor : Constructor := { src_c with argTypes := newArgs }
    have hmd_c_eq : md_c = newCtor := by
      have h1 := Option.some.inj hmd_get
      injection h1 with _ h2
      exact h2.symm
    intro t' ht'_mem g args mono hcontain
    rw [hmd_c_eq] at ht'_mem
    -- ht'_mem : t' ∈ newCtor.argTypes = newArgs = src_c.argTypes.map (...)
    show ∃ concName, mono[(g, args)]? = some concName
    have ht'_in_newArgs : t' ∈ newArgs := ht'_mem
    obtain ⟨src_t, hsrc_t_mem, ht'_eq⟩ := List.mem_map.mp ht'_in_newArgs
    have hCov_src_t : Typ.AllAppsP (fun g args => (g, args) ∈ drained.seen) src_t :=
      hCov_src src_t hsrc_t_mem
    rw [← ht'_eq] at hcontain
    exact RefClosedBody.appsResolved_via_seen_coverage_rewrite
      hSSM hCov_src_t mono g args hcontain
  · -- (B) newDt case: use `concretizeBuild_at_newDt_ctor_name_explicit` to extract
    -- `md_c.argTypes = c'.argTypes.map (rewriteTyp ∅ drained.mono)` for some
    -- `c' ∈ dt'.constructors, dt' ∈ drained.newDataTypes`. AppsReachedCond newDt
    -- clause gives `AllAppsP (∈ seen)` for `c'.argTypes`.
    have hcd_at_name : ∃ d, cd.getByKey name = some d := hcd_at_name
    rw [← hpush_eq] at hmd_get hcd_at_name
    -- Disjointness premises (mirror umbrella ctor-newDt arm).
    have hDtNotKey : ∀ dt' ∈ drained.newDataTypes,
        dt'.name ≠ dt_new.name.pushNamespace c_new.nameHead := by
      intro dt' hmem heq
      let collisionArg : Typ := .ref ⟨.mkSimple c_new.nameHead⟩
      have hLHS_eq : concretizeName dt_new.name #[collisionArg] =
          dt_new.name.pushNamespace c_new.nameHead :=
        RefClosedBody.concretizeName_singleton_ref_simple dt_new.name c_new.nameHead
      have hdt'_eq : dt'.name = concretizeName dt_new.name #[collisionArg] := by
        rw [hLHS_eq]; exact heq
      obtain ⟨g_orig', args', dt_orig', hname_eq', hdt_orig_get', hsz', _⟩ :=
        hSNN.2 dt' hmem
      obtain ⟨g_new_orig, args_new, dt_new_orig, hname_eq_new, hdt_new_get,
              hsz_new, _⟩ := hSNN.2 dt_new hdt_new_mem
      have heq1 : concretizeName g_orig' args' =
          concretizeName dt_new.name #[collisionArg] := by
        rw [← hname_eq', hdt'_eq]
      have hKey1 : ∃ d, cd.getByKey (concretizeName g_orig' args') = some d := by
        rw [heq1, hLHS_eq]; exact hcd_at_name
      obtain ⟨hgo_eq, hargs_eq⟩ :=
        hUnique hconc g_orig' dt_new.name args' #[collisionArg] heq1 hKey1
      have hsz_args' : args'.size = 1 := by rw [hargs_eq]; rfl
      have heq2 : concretizeName g_new_orig args_new =
          concretizeName dt_new.name #[] := by
        rw [concretizeName_empty_args, ← hname_eq_new]
      have hconc_fold : (concretizeBuild tds drained.mono drained.newFunctions
            drained.newDataTypes).foldlM (init := default) step4Lower = .ok cd := by
        have hconc_eq := hconc
        unfold Typed.Decls.concretize at hconc_eq
        simp only [bind, Except.bind] at hconc_eq
        rw [hdrain] at hconc_eq
        exact hconc_eq
      have hKey2 : ∃ d, cd.getByKey (concretizeName g_new_orig args_new) = some d := by
        rw [← hname_eq_new]
        exact RefClosedBody.cd_has_some_at_newDt_name hconc_fold hdt_new_mem
      obtain ⟨hg_new_eq, hargs_new_eq⟩ :=
        hUnique hconc g_new_orig dt_new.name args_new #[] heq2 hKey2
      have hsz_an : args_new.size = 0 := by rw [hargs_new_eq]; rfl
      have hg_cross : g_orig' = g_new_orig := by rw [hgo_eq, hg_new_eq]
      rw [hg_cross] at hdt_orig_get'
      rw [hdt_new_get] at hdt_orig_get'
      have hdt_eq : dt_orig' = dt_new_orig := by
        have h1 : Typed.Declaration.dataType dt_new_orig =
            .dataType dt_orig' := Option.some.inj hdt_orig_get'
        injection h1.symm
      rw [hdt_eq] at hsz'
      rw [hsz_args'] at hsz'
      rw [hsz_an] at hsz_new
      omega
    have hFnNotKey : ∀ f ∈ drained.newFunctions,
        f.name ≠ dt_new.name.pushNamespace c_new.nameHead := by
      intro f hmem heq
      let collisionArg : Typ := .ref ⟨.mkSimple c_new.nameHead⟩
      have hLHS_eq : concretizeName dt_new.name #[collisionArg] =
          dt_new.name.pushNamespace c_new.nameHead :=
        RefClosedBody.concretizeName_singleton_ref_simple dt_new.name c_new.nameHead
      have hf_eq : f.name = concretizeName dt_new.name #[collisionArg] := by
        rw [hLHS_eq]; exact heq
      obtain ⟨g_f, args_f, f_orig, hf_name, hf_get, _⟩ := hSNN.1 f hmem
      have heq' : concretizeName g_f args_f = concretizeName dt_new.name #[collisionArg] := by
        rw [← hf_name, hf_eq]
      have hKey : ∃ d, cd.getByKey (concretizeName g_f args_f) = some d := by
        rw [heq', hLHS_eq]; exact hcd_at_name
      obtain ⟨hg_eq, hargs_eq⟩ :=
        hUnique hconc g_f dt_new.name args_f #[collisionArg] heq' hKey
      -- args_f.size = 1.
      have hsz_args_f : args_f.size = 1 := by rw [hargs_eq]; rfl
      -- tds at g_f = .function f_orig. But also g_f = dt_new.name.
      -- dt_new.name = concretizeName g_new_orig args_new with args_new.size = 0,
      -- so tds at dt_new.name (via SNN) = some .dataType. Conflict with .function.
      obtain ⟨g_new_orig, args_new, dt_new_orig, hname_eq_new, hdt_new_get,
              hsz_new, _⟩ := hSNN.2 dt_new hdt_new_mem
      have heq2 : concretizeName g_new_orig args_new =
          concretizeName dt_new.name #[] := by
        rw [concretizeName_empty_args, ← hname_eq_new]
      have hconc_fold : (concretizeBuild tds drained.mono drained.newFunctions
            drained.newDataTypes).foldlM (init := default) step4Lower = .ok cd := by
        have hconc_eq := hconc
        unfold Typed.Decls.concretize at hconc_eq
        simp only [bind, Except.bind] at hconc_eq
        rw [hdrain] at hconc_eq
        exact hconc_eq
      have hKey2 : ∃ d, cd.getByKey (concretizeName g_new_orig args_new) = some d := by
        rw [← hname_eq_new]
        exact RefClosedBody.cd_has_some_at_newDt_name hconc_fold hdt_new_mem
      obtain ⟨hg_new_eq, _⟩ :=
        hUnique hconc g_new_orig dt_new.name args_new #[] heq2 hKey2
      rw [hg_eq, ← hg_new_eq] at hf_get
      rw [hdt_new_get] at hf_get; cases hf_get
    -- Apply explicit lemma to identify md_c's structure.
    obtain ⟨md_at_name, hmd_at_get, hCAR⟩ :=
      PhaseA2.concretizeBuild_at_newDt_ctor_name_explicit tds drained.mono
        drained.newFunctions drained.newDataTypes hdt_new_mem hc_new_mem
        hDtNotKey hFnNotKey
    rw [hmd_at_get] at hmd_get
    have hmd_eq : md_at_name = .constructor md_dt md_c := Option.some.inj hmd_get
    rw [hmd_eq] at hCAR
    obtain ⟨md_dt', md_c', hcons_eq, dt', hdt'_mem, c', hc'_mem, hargs_map⟩ := hCAR
    have hmdc_eq : md_c = md_c' := by
      have h1 : Typed.Declaration.constructor md_dt md_c =
          .constructor md_dt' md_c' := hcons_eq
      injection h1
    rw [← hmdc_eq] at hargs_map
    -- hargs_map : md_c.argTypes = c'.argTypes.map (rewriteTyp ∅ drained.mono).
    -- AppsReachedCond newDt clause for c'.argTypes via dt' ∈ newDataTypes.
    have hdt'_mem_arr : dt' ∈ drained.newDataTypes :=
      Array.mem_toList_iff.mp hdt'_mem
    have hCov_new := AppsReachedCond_newDt_AllAppsP_seen_post_drain hARC hPE hdt'_mem_arr
    intro t' ht'_mem g args mono hcontain
    rw [hargs_map] at ht'_mem
    obtain ⟨src_t, hsrc_t_mem, ht'_eq⟩ := List.mem_map.mp ht'_mem
    have hCov_src_t : Typ.AllAppsP (fun g args => (g, args) ∈ drained.seen) src_t :=
      hCov_new c' hc'_mem src_t hsrc_t_mem
    rw [← ht'_eq] at hcontain
    exact RefClosedBody.appsResolved_via_seen_coverage_rewrite
      hSSM hCov_src_t mono g args hcontain

/-- **Entry-restricted `concretize_produces_refClosed`.**

Same conclusion (`Concrete.Decls.RefClosed cd`) as `concretize_produces_refClosed`,
but takes only `WellFormed t` together with the `mkDecls` / `checkAndSimplify` /
`concretize` pipeline witnesses — no `FullyMonomorphic t`.

`RefClosed cd` is a property of `cd` alone (universal over the keys present in
`cd`). Since `concretize`'s drain only emits monomorphic instances reachable
from entries, every type-ref appearing in `cd` resolves to a key that is itself
present in `cd`. The realistic closure path therefore derives `RefClosed cd`
directly from the drained-mono shape of `cd` (via `DrainState` invariants),
NOT via `AllRefsAreDtKeys tds` (which is structurally false for polymorphic
source).

Body F=1 framework (revised 2026-04-30 — earlier "F=0" claim was incorrect:
the F=0 path was via `concretize_produces_refClosed` (RefClosed.lean:2093)
which consumes `FullyMonomorphic t`, removed from `WellFormed` 2026-04-26).

Mock-first applied: body decomposed into 4 named `have`-stubs:
- `h_inputs : ∀ lt ∈ f.inputs, Concrete.Typ.RefClosed cd lt.snd`
- `h_output : Concrete.Typ.RefClosed cd f.output`
- `h_dt    : ∀ c ∈ dt.constructors, ∀ t ∈ c.argTypes, Concrete.Typ.RefClosed cd t`
- `h_c     : ∀ t ∈ c.argTypes, Concrete.Typ.RefClosed cd t`

Closure requires TWO new infra pieces (~160 LoC, audit 2026-04-30):

1. `typToConcrete_RefClosed_via_StrongNewNameShape` (~80 LoC):
   ```
   typToConcrete mono t_typed = .ok t_cd →
   (∀ g ∈ refsOf t_typed, ∃ dt, cd.getByKey g = some (.dataType dt)) →
   Concrete.Typ.RefClosed cd t_cd
   ```
   Mirror `typToConcrete_preserves_RefTargetsInTds` (RefClosed.lean:916).

2. `Typed.Typ.AppRefToDt` predicate + preservation (~80 LoC):
   `.app g args ⇒ tds.getByKey g = some (.dataType _)`. Source-side
   `SrcTypRefsAreDtKeys` (CheckSound.lean:1596) already exists; lift to typed
   via existing `checkAndSimplify` chain. Required to discharge premise (1)
   for `.app g args` whose mono-lookup hits in cd.

Per-arm closure path:
* `.function`: `step4Lower_backward_function_kind_at_key` (Phase4.lean:607)
  → `concretizeBuild_function_origin` (SizeBound.lean:487) → apply new helper.
* `.dataType`: `step4Lower_backward_dataType_kind_at_key` (Phase4.lean:583)
  → `concretizeBuild_dataType_origin` (SizeBound.lean:142) → new helper.
* `.constructor`: `step4Lower_backward_ctor_kind_at_key` (Phase4.lean:633)
  → concretizeBuild origin → new helper.

cd-side dt-presence at `g'` derives from `StrongNewNameShape`
(`concretize_drain_preserves_StrongNewNameShape`, Shapes.lean:104):
every `.ref g'` in monoDecls has `g' = concretizeName g_orig args` for
some tds-keyed dt_orig. step4Lower forward-preserves keys.

Total: ~80 (helper) + ~100/arm × 3 = ~380 LoC. -/
theorem Toplevel.concretize_produces_refClosed_entry
    {t : Source.Toplevel} {decls : Source.Decls} {tds : Typed.Decls}
    {cd : Concrete.Decls}
    (_hwf : WellFormed t)
    (_hdecls : t.mkDecls = .ok decls)
    (_hts : t.checkAndSimplify = .ok tds)
    (_hconc : tds.concretize = .ok cd) :
    Concrete.Decls.RefClosed cd := by
  intro name d hget
  -- Mock-first: state expected sub-claims as `have`s with sorry'd RHS.
  -- Each will extract to a global helper once shape verifies.
  match d, hget with
  | .function f, hget =>
    -- Drain extraction.
    have hconc' := _hconc
    unfold Typed.Decls.concretize at hconc'
    simp only [bind, Except.bind] at hconc'
    split at hconc'
    · cases hconc'
    rename_i drained hdrain
    have hSNN : drained.StrongNewNameShape tds :=
      concretize_drain_preserves_StrongNewNameShape _ _
        (DrainState.StrongNewNameShape.init tds (concretizeSeed tds)) hdrain
    have hMonoShape : drained.MonoShapeOk tds :=
      concretize_drain_shape_equation _ _
        (DrainState.MonoShapeOk.init tds (concretizeSeed tds)) hdrain
    have hNFFS : drained.NewFnFullShape tds :=
      concretize_drain_preserves_NewFnFullShape _ _
        (DrainState.NewFnFullShape.init tds (concretizeSeed tds)) hdrain
    have hUnique : Typed.Decls.ConcretizeUniqueNames tds :=
      _hwf.noNameCollisions _ _hts
    -- New 2026-04-30: AppsReachedCond + SeenSubsetMono + pending=∅ for the
    -- entry-restricted `appsResolved` discharge at the 4 sorry sites.
    have hSSM : drained.SeenSubsetMono :=
      concretize_drain_preserves_SeenSubsetMono _ _
        (DrainState.SeenSubsetMono.init _) hdrain
    have hARC : drained.AppsReachedCond tds :=
      concretize_drain_preserves_AppsReachedCond _ _
        (DrainState.AppsReachedCond.init tds) hdrain
    have hPE_b : drained.pending.isEmpty :=
      concretize_drain_succeeds_pending_empty _ _ hdrain
    have hPE : ∀ q, q ∈ drained.pending → False := by
      intro q hq
      have hne : drained.pending.isEmpty = false := by
        rw [Std.HashSet.isEmpty_eq_false_iff_exists_contains_eq_true]
        exact ⟨q, Std.HashSet.contains_iff_mem.mpr hq⟩
      rw [hne] at hPE_b; cases hPE_b
    -- Backward + forward step4Lower.
    obtain ⟨md_f, hmd_get⟩ :=
      step4Lower_backward_function_kind_at_key hget hconc'
    obtain ⟨cd_f', hcd_get_full, _hname_eq, hinputs_witness, houtput_witness⟩ :=
      step4Lower_function_explicit hmd_get hconc'
    have hsame : (Concrete.Declaration.function cd_f') = .function f := by
      rw [hcd_get_full] at hget
      exact (Option.some.injEq _ _).mp hget
    have heq_f : cd_f' = f := by injection hsame
    rw [heq_f] at hinputs_witness houtput_witness
    -- AppRefToDtOrNewDt for md_f.inputs (.snd) and md_f.output. Origin split.
    have h_md_AR_combined : (∀ t' ∈ md_f.inputs.map (·.2),
          RefClosedBody.Typed.Typ.AppRefToDtOrNewDt tds drained.newDataTypes t') ∧
        RefClosedBody.Typed.Typ.AppRefToDtOrNewDt tds drained.newDataTypes md_f.output := by
      rcases DirectDagBody.concretizeBuild_function_origin tds drained.mono drained.newFunctions
          drained.newDataTypes hmd_get with
        ⟨src_f, hsrc_get, hsrc_params⟩ | ⟨fn_new, hfn_new_mem, hfn_new_name⟩
      · -- (A) source case.
        have hcd_at_name : ∃ d, cd.getByKey name = some d := ⟨_, hcd_get_full⟩
        have hDtNotKey : ∀ dt' ∈ drained.newDataTypes, dt'.name ≠ name := by
          intro dt' hmem heq
          obtain ⟨g_orig, args, dt_orig, hname_eq', hdt_orig_get, _, _⟩ :=
            hSNN.2 dt' hmem
          have heq' : concretizeName g_orig args = concretizeName name #[] := by
            rw [← hname_eq', heq, concretizeName_empty_args]
          have hKey : ∃ d, cd.getByKey (concretizeName g_orig args) = some d := by
            rw [heq', concretizeName_empty_args]; exact hcd_at_name
          obtain ⟨hg_eq, _⟩ := hUnique _hconc g_orig name args #[] heq' hKey
          rw [hg_eq] at hdt_orig_get
          rw [hsrc_get] at hdt_orig_get
          have h_inj : Typed.Declaration.function src_f = .dataType dt_orig :=
            Option.some.inj hdt_orig_get
          cases h_inj
        have hCtorNotKey : ∀ dt' ∈ drained.newDataTypes, ∀ c ∈ dt'.constructors,
            dt'.name.pushNamespace c.nameHead ≠ name := by
          intro dt' hmem c hc heq
          let collisionArg : Typ := .ref ⟨.mkSimple c.nameHead⟩
          have hLHS_eq : concretizeName dt'.name #[collisionArg] =
              dt'.name.pushNamespace c.nameHead :=
            RefClosedBody.concretizeName_singleton_ref_simple dt'.name c.nameHead
          have heq_concName :
              concretizeName dt'.name #[collisionArg] = concretizeName name #[] := by
            rw [hLHS_eq, heq, concretizeName_empty_args]
          have hKey : ∃ d, cd.getByKey (concretizeName dt'.name #[collisionArg]) = some d := by
            rw [hLHS_eq, heq]; exact hcd_at_name
          obtain ⟨_, hargs_eq⟩ :=
            hUnique _hconc dt'.name name #[collisionArg] #[] heq_concName hKey
          have h1 : (#[collisionArg] : Array Typ).size = 1 := rfl
          have h0 : (#[collisionArg] : Array Typ).size = 0 := by rw [hargs_eq]; rfl
          omega
        -- Drain MAY emit a newFn at `name` (when collectCalls picks up a
        -- monomorphic call to `name` in some body). In that case, fnStep
        -- overrides srcStep's insert at `name`. We case-split.
        by_cases hOverride : ∃ f' ∈ drained.newFunctions, f'.name = name
        · -- Override sub-case: identify md_f.inputs/output via the newFn
          -- explicit form. The override f' has shape derived from src_f via
          -- `NewFnFullShape` + tds-value-uniqueness + empty-substitution
          -- collapse, so md_f's structure matches the source path's monoF.
          obtain ⟨f', hf'_mem, hf'_name⟩ := hOverride
          -- Use FullShape to identify f' in terms of src_f.
          obtain ⟨g_orig, args, f_orig, _hin_seen, hf_orig_get, hsz, hf'_shape⟩ :=
            hNFFS f' hf'_mem
          have hf'_name' : f'.name = concretizeName g_orig args := by
            rw [hf'_shape]
          have heq' : concretizeName g_orig args = concretizeName name #[] := by
            rw [← hf'_name', hf'_name, concretizeName_empty_args]
          have hKey : ∃ d, cd.getByKey (concretizeName g_orig args) = some d := by
            rw [heq', concretizeName_empty_args]; exact hcd_at_name
          obtain ⟨hg_eq, hargs_eq⟩ :=
            hUnique _hconc g_orig name args #[] heq' hKey
          -- Establish f_orig = src_f via tds value uniqueness at name.
          rw [hg_eq] at hf_orig_get
          rw [hsrc_get] at hf_orig_get
          have hf_orig_eq : f_orig = src_f := by
            have h1 : Typed.Declaration.function src_f = .function f_orig :=
              Option.some.inj hf_orig_get
            injection h1.symm
          have hsubst_empty : mkParamSubst f_orig.params args = fun _ => none := by
            rw [hf_orig_eq, hsrc_params, hargs_eq]
            funext g; simp [mkParamSubst]
          -- Apply override-aware explicit lemma.
          have hOtherFnNotKey : ∀ f'' ∈ drained.newFunctions, f'' ≠ f' →
              f''.name ≠ f'.name := by
            intro f'' hf''_mem hne heq2
            obtain ⟨g2, args2, f_orig2, _, hf_orig2_get, _, hf''_shape⟩ :=
              hNFFS f'' hf''_mem
            obtain ⟨g1, args1, f_orig1, _, hf_orig1_get, _, hf'_shape'⟩ :=
              hNFFS f' hf'_mem
            have hname_f'' : f''.name = concretizeName g2 args2 := by
              rw [hf''_shape]
            have hname_f' : f'.name = concretizeName g1 args1 := by
              rw [hf'_shape']
            have heq1 : concretizeName g2 args2 = concretizeName g1 args1 := by
              rw [← hname_f'', heq2, hname_f']
            have hKey1 : ∃ d, cd.getByKey (concretizeName g2 args2) = some d := by
              rw [heq1, ← hname_f', hf'_name]; exact hcd_at_name
            obtain ⟨hg_eq', hargs_eq'⟩ :=
              hUnique _hconc g2 g1 args2 args1 heq1 hKey1
            rw [hg_eq'] at hf_orig2_get
            rw [hf_orig1_get] at hf_orig2_get
            have hf_orig_eq' : f_orig2 = f_orig1 := by
              have h1 : Typed.Declaration.function f_orig1 =
                  .function f_orig2 := Option.some.inj hf_orig2_get
              injection h1.symm
            apply hne
            rw [hf''_shape, hf'_shape', hg_eq', hargs_eq', hf_orig_eq']
          obtain ⟨md_f_at, hmd_at_get_fn, _hName_fn, hInputs_fn, hOutput_fn, _hBody_fn⟩ :=
            PhaseA2.concretizeBuild_at_newFn_name_full_explicit tds drained.mono
              drained.newFunctions drained.newDataTypes hf'_mem hOtherFnNotKey
          rw [hf'_name] at hmd_at_get_fn
          rw [hmd_at_get_fn] at hmd_get
          have hmd_eq : md_f_at = md_f := by
            have h1 : Typed.Declaration.function md_f_at = .function md_f :=
              Option.some.inj hmd_get
            injection h1
          rw [hmd_eq] at hInputs_fn hOutput_fn
          -- Translate f'.inputs/output to src_f.inputs/output via
          -- NewFnFullShape + empty-subst collapse.
          have hf'_inputs_proj : f'.inputs = f_orig.inputs.map fun (l, t) =>
              (l, Typ.instantiate (mkParamSubst f_orig.params args) t) := by
            rw [hf'_shape]
          have hf'_output_proj : f'.output =
              Typ.instantiate (mkParamSubst f_orig.params args) f_orig.output := by
            rw [hf'_shape]
          have hf'_inputs_id : f'.inputs = src_f.inputs := by
            rw [hf'_inputs_proj, hsubst_empty, hf_orig_eq]
            -- Goal: src_f.inputs.map (l, t) => (l, Typ.instantiate ∅ t) = src_f.inputs.
            induction src_f.inputs with
            | nil => rfl
            | cons hd tl ih =>
              cases hd with
              | mk l t =>
                show (l, Typ.instantiate (fun _ => none) t) ::
                    tl.map (fun (lt : Local × Typ) =>
                      (lt.1, Typ.instantiate (fun _ => none) lt.2)) =
                  (l, t) :: tl
                rw [Typ.instantiate_empty_id, ih]
          have hf'_output_eq : f'.output = src_f.output := by
            rw [hf'_output_proj, hsubst_empty, hf_orig_eq, Typ.instantiate_empty_id]
          -- Rewrite md_f.inputs/output to use src_f instead of f'.
          rw [hf'_inputs_id] at hInputs_fn
          rw [hf'_output_eq] at hOutput_fn
          -- Now md_f.inputs = src_f.inputs.map ..., md_f.output = rewriteTyp ∅ mono src_f.output.
          -- Source-side wellFormedness path (same as no-override branch).
          have hP := FnMatchP_checkAndSimplify _hdecls _hts
          obtain ⟨src_f_decl, hsrc_decl, _hinputs_eq⟩ := (hP name).1 src_f hsrc_get
          have hwf_src := checkAndSimplify_implies_wellFormedDecls _hdecls _hts
          have hsrc_pair :
              (name, Source.Declaration.function src_f_decl) ∈ decls.pairs.toList :=
            IndexMap.mem_pairs_of_getByKey _ _ _ hsrc_decl
          obtain ⟨_vis, _vis', hwf_step⟩ :=
            wellFormedDecls_reflect_pair hwf_src name (.function src_f_decl) hsrc_pair
          have hwf_pair := wellFormedDecls_reflect_function hwf_step
          have hparams_decl : src_f_decl.params = [] := by
            have := checkAndSimplify_preserves_params _hdecls _hts hsrc_decl hsrc_get
            rw [hsrc_params] at this
            exact this.symm
          have h_dt_lift : ∀ g, (∃ dt_src, decls.getByKey g = some (.dataType dt_src)) →
              ∃ dt_td, tds.getByKey g = some (.dataType dt_td) := by
            intro g ⟨dt_src, hget_src⟩
            obtain ⟨dt_td, hget_td⟩ := checkAndSimplify_src_dt_to_td _hdecls _hts hget_src
            exact ⟨dt_td, hget_td⟩
          have h_dt_params_lift : ∀ g,
              (∃ dt_src, decls.getByKey g = some (.dataType dt_src) ∧ dt_src.params = []) →
              ∃ dt_td, tds.getByKey g = some (.dataType dt_td) ∧ dt_td.params = [] := by
            intro g ⟨dt_src, hget_src, hparams⟩
            obtain ⟨dt_td, hget_td⟩ := checkAndSimplify_src_dt_to_td _hdecls _hts hget_src
            have hsrc' : decls.getByKey g = some (.dataType dt_td) := (hP g).2.1 dt_td hget_td
            have h1 : Source.Declaration.dataType dt_src = .dataType dt_td := by
              rw [hget_src] at hsrc'
              exact Option.some.inj hsrc'
            have hdt_eq : dt_src = dt_td := by injection h1
            exact ⟨dt_td, hget_td, hdt_eq ▸ hparams⟩
          refine ⟨?_, ?_⟩
          · -- inputs
            intro t' ht'_mem
            obtain ⟨lt, hlt_mem, ht'_eq⟩ := List.mem_map.mp ht'_mem
            rw [hInputs_fn] at hlt_mem
            obtain ⟨src_lt, hsrc_lt_mem, hlt_eq⟩ := List.mem_map.mp hlt_mem
            rw [← hlt_eq] at ht'_eq
            subst ht'_eq
            have hsrc_lt_in_decl : src_lt ∈ src_f_decl.inputs := by
              rw [_hinputs_eq] at hsrc_lt_mem
              exact hsrc_lt_mem
            have hwf_t : wellFormedDecls.wellFormedType decls src_f_decl.params src_lt.2 = .ok () :=
              hwf_pair.2 src_lt hsrc_lt_in_decl
            rw [hparams_decl] at hwf_t
            have hSRD := SrcTypRefsAreDtKeys_of_wellFormedType decls [] src_lt.2 hwf_t
            have hAR := RefClosedBody.AppRefToDt_of_SrcTypRefsAreDtKeys
              h_dt_lift h_dt_params_lift hSRD
            exact RefClosedBody.rewriteTyp_preserves_AppRefToDtOrNewDt hMonoShape hAR
          · -- output
            have hwf_out : wellFormedDecls.wellFormedType decls src_f_decl.params src_f_decl.output
                = .ok () := hwf_pair.1
            rw [hparams_decl] at hwf_out
            have houtput_eq : src_f.output = src_f_decl.output :=
              checkAndSimplify_preserves_output _hdecls _hts hsrc_decl hsrc_get
            rw [hOutput_fn]
            show RefClosedBody.Typed.Typ.AppRefToDtOrNewDt tds drained.newDataTypes
                (rewriteTyp (fun _ => none) drained.mono src_f.output)
            rw [houtput_eq]
            have hSRD := SrcTypRefsAreDtKeys_of_wellFormedType decls [] src_f_decl.output hwf_out
            have hAR := RefClosedBody.AppRefToDt_of_SrcTypRefsAreDtKeys
              h_dt_lift h_dt_params_lift hSRD
            exact RefClosedBody.rewriteTyp_preserves_AppRefToDtOrNewDt hMonoShape hAR
        -- No-override sub-case: existing source-mono path.
        have hFnNotKey : ∀ f' ∈ drained.newFunctions, f'.name ≠ name := by
          intro f' hf'_mem hf'_name
          exact hOverride ⟨f', hf'_mem, hf'_name⟩
        -- Apply explicit fn form.
        have hexplicit :=
          PhaseA2.concretizeBuild_at_typed_function_explicit tds drained.mono
            drained.newFunctions drained.newDataTypes hsrc_get hsrc_params
            hDtNotKey hFnNotKey hCtorNotKey
        rw [hexplicit] at hmd_get
        let monoF : Typed.Function :=
          { src_f with
            inputs := src_f.inputs.map fun (l, t) =>
              (l, rewriteTyp (fun _ => none) drained.mono t),
            output := rewriteTyp (fun _ => none) drained.mono src_f.output,
            body := rewriteTypedTerm tds (fun _ => none) drained.mono src_f.body }
        have hmd_f_eq : md_f = monoF := by
          have h1 : Typed.Declaration.function monoF = .function md_f :=
            Option.some.inj hmd_get
          have h2 : monoF = md_f := by injection h1
          exact h2.symm
        rw [hmd_f_eq]
        -- Source-side wellFormedness.
        have hP := FnMatchP_checkAndSimplify _hdecls _hts
        obtain ⟨src_f_decl, hsrc_decl, _hinputs_eq⟩ := (hP name).1 src_f hsrc_get
        have hwf_src := checkAndSimplify_implies_wellFormedDecls _hdecls _hts
        have hsrc_pair :
            (name, Source.Declaration.function src_f_decl) ∈ decls.pairs.toList :=
          IndexMap.mem_pairs_of_getByKey _ _ _ hsrc_decl
        obtain ⟨_vis, _vis', hwf_step⟩ :=
          wellFormedDecls_reflect_pair hwf_src name (.function src_f_decl) hsrc_pair
        have hwf_pair := wellFormedDecls_reflect_function hwf_step
        -- src_f_decl.params = src_f.params = [].
        have hparams_decl : src_f_decl.params = [] := by
          have := checkAndSimplify_preserves_params _hdecls _hts hsrc_decl hsrc_get
          rw [hsrc_params] at this
          exact this.symm
        -- Lift wellFormedness to AppRefToDtOrNewDt.
        have h_dt_lift : ∀ g, (∃ dt_src, decls.getByKey g = some (.dataType dt_src)) →
            ∃ dt_td, tds.getByKey g = some (.dataType dt_td) := by
          intro g ⟨dt_src, hget_src⟩
          obtain ⟨dt_td, hget_td⟩ := checkAndSimplify_src_dt_to_td _hdecls _hts hget_src
          exact ⟨dt_td, hget_td⟩
        have h_dt_params_lift : ∀ g,
            (∃ dt_src, decls.getByKey g = some (.dataType dt_src) ∧ dt_src.params = []) →
            ∃ dt_td, tds.getByKey g = some (.dataType dt_td) ∧ dt_td.params = [] := by
          intro g ⟨dt_src, hget_src, hparams⟩
          obtain ⟨dt_td, hget_td⟩ := checkAndSimplify_src_dt_to_td _hdecls _hts hget_src
          have hsrc' : decls.getByKey g = some (.dataType dt_td) := (hP g).2.1 dt_td hget_td
          have h1 : Source.Declaration.dataType dt_src = .dataType dt_td := by
            rw [hget_src] at hsrc'
            exact Option.some.inj hsrc'
          have hdt_eq : dt_src = dt_td := by injection h1
          exact ⟨dt_td, hget_td, hdt_eq ▸ hparams⟩
        refine ⟨?_, ?_⟩
        · -- inputs
          intro t' ht'_mem
          obtain ⟨lt, hlt_mem, ht'_eq⟩ := List.mem_map.mp ht'_mem
          obtain ⟨src_lt, hsrc_lt_mem, hlt_eq⟩ := List.mem_map.mp hlt_mem
          rw [← hlt_eq] at ht'_eq
          subst ht'_eq
          have hsrc_lt_in_decl : src_lt ∈ src_f_decl.inputs := by
            -- src_f_decl.inputs.map (·.snd) = src_f.inputs.map (·.snd) (via FnMatchP gives inputs eq).
            -- Wait FnMatchP.1 returns ⟨f, hsrc, tf.inputs = f.inputs⟩.
            -- So src_f_decl.inputs = src_f.inputs (typed-side).
            -- Wait actual: hinputs_eq : src_f.inputs = src_f_decl.inputs (or other direction).
            -- hP (HfM.1): tf.inputs = f.inputs where tf is typed, f is source.
            -- So src_f.inputs = src_f_decl.inputs.
            rw [_hinputs_eq] at hsrc_lt_mem
            exact hsrc_lt_mem
          have hwf_t : wellFormedDecls.wellFormedType decls src_f_decl.params src_lt.2 = .ok () :=
            hwf_pair.2 src_lt hsrc_lt_in_decl
          rw [hparams_decl] at hwf_t
          have hSRD := SrcTypRefsAreDtKeys_of_wellFormedType decls [] src_lt.2 hwf_t
          have hAR := RefClosedBody.AppRefToDt_of_SrcTypRefsAreDtKeys
            h_dt_lift h_dt_params_lift hSRD
          exact RefClosedBody.rewriteTyp_preserves_AppRefToDtOrNewDt hMonoShape hAR
        · -- output
          have hwf_out : wellFormedDecls.wellFormedType decls src_f_decl.params src_f_decl.output
              = .ok () := hwf_pair.1
          rw [hparams_decl] at hwf_out
          have houtput_eq : src_f.output = src_f_decl.output :=
            checkAndSimplify_preserves_output _hdecls _hts hsrc_decl hsrc_get
          show RefClosedBody.Typed.Typ.AppRefToDtOrNewDt tds drained.newDataTypes
              (rewriteTyp (fun _ => none) drained.mono src_f.output)
          rw [houtput_eq]
          have hSRD := SrcTypRefsAreDtKeys_of_wellFormedType decls [] src_f_decl.output hwf_out
          have hAR := RefClosedBody.AppRefToDt_of_SrcTypRefsAreDtKeys
            h_dt_lift h_dt_params_lift hSRD
          exact RefClosedBody.rewriteTyp_preserves_AppRefToDtOrNewDt hMonoShape hAR
      · -- (B) newDt case: fn_new ∈ drained.newFunctions with fn_new.name = name.
        -- Drain emits fn_new with inputs/output via Typ.instantiate of the source
        -- function template under (g_orig, args). md_f comes from fnStep applied
        -- to fn_new, which wraps inputs/output via rewriteTyp ∅ drained.mono.
        -- Closure: `concretize_produces_NewFnInputs/OutputAppRefToDt` gives
        -- AppRefToDt-safety of fn_new.inputs/.output; rewriteTyp lifts to
        -- AppRefToDtOrNewDt.
        have hcd_at_name : ∃ d, cd.getByKey name = some d := ⟨_, hcd_get_full⟩
        rw [← hfn_new_name] at hmd_get hcd_at_name
        -- Disjointness: any other f' ∈ drained.newFunctions with f'.name = fn_new.name
        -- forces f' = fn_new (via SNN + hUnique + value-uniqueness in tds).
        have hOtherFnNotKey : ∀ f' ∈ drained.newFunctions, f' ≠ fn_new →
            f'.name ≠ fn_new.name := by
          intro f' hf'_mem hne heq
          -- FullShape gives canonical push origin for both fns.
          obtain ⟨g_orig, args, f_orig, _, hf_get, _, hshape⟩ :=
            hNFFS f' hf'_mem
          obtain ⟨g_new_orig, args_new, fn_new_orig, _, hf_new_get, _, hshape_new⟩ :=
            hNFFS fn_new hfn_new_mem
          -- Names: f'.name = cN g_orig args, fn_new.name = cN g_new_orig args_new.
          have hname_f' : f'.name = concretizeName g_orig args := by
            rw [hshape]
          have hname_fn : fn_new.name = concretizeName g_new_orig args_new := by
            rw [hshape_new]
          have heq1 : concretizeName g_orig args =
              concretizeName g_new_orig args_new := by
            rw [← hname_f', heq, hname_fn]
          -- cd-key witness via fn_new.name (from hcd_at_name post-rewrite).
          have hKey1 : ∃ d, cd.getByKey (concretizeName g_orig args) = some d := by
            rw [heq1, ← hname_fn]; exact hcd_at_name
          obtain ⟨hg_eq, hargs_eq⟩ :=
            hUnique _hconc g_orig g_new_orig args args_new heq1 hKey1
          -- f_orig = fn_new_orig (same tds key g_orig = g_new_orig).
          rw [hg_eq] at hf_get
          rw [hf_new_get] at hf_get
          have hf_orig_eq : f_orig = fn_new_orig := by
            have h1 : Typed.Declaration.function fn_new_orig =
                .function f_orig := Option.some.inj hf_get
            injection h1.symm
          -- Both f' and fn_new equal the canonical push shape for the same
          -- (g, args, f_orig) — hence f' = fn_new, contradicting hne.
          apply hne
          rw [hshape, hshape_new, hg_eq, hargs_eq, hf_orig_eq]
        -- Apply explicit-form lemma to identify md_f's structure.
        obtain ⟨md_f_at, hmd_at_get_fn, hName_fn, hInputs_fn, hOutput_fn, _hBody_fn⟩ :=
          PhaseA2.concretizeBuild_at_newFn_name_full_explicit tds drained.mono
            drained.newFunctions drained.newDataTypes hfn_new_mem hOtherFnNotKey
        rw [hmd_at_get_fn] at hmd_get
        have hmd_eq : md_f_at = md_f := by
          have h1 : Typed.Declaration.function md_f_at = .function md_f :=
            Option.some.inj hmd_get
          injection h1
        rw [hmd_eq] at hInputs_fn hOutput_fn hName_fn
        -- Drain invariants: fn_new.inputs/.output AppRefToDt-safe.
        have hFnInInv : drained.NewFnInputsAppRefToDt tds :=
          concretize_produces_NewFnInputsAppRefToDt _hwf _hdecls _hts hdrain
        have hFnOutInv : drained.NewFnOutputAppRefToDt tds :=
          concretize_produces_NewFnOutputAppRefToDt _hwf _hdecls _hts hdrain
        refine ⟨?_, ?_⟩
        · -- inputs: each t' ∈ md_f.inputs.map (·.2) is AppRefToDtOrNewDt.
          intro t' ht'_mem
          obtain ⟨lt, hlt_mem, ht'_eq⟩ := List.mem_map.mp ht'_mem
          subst ht'_eq
          -- md_f.inputs = fn_new.inputs.map (l,t) ↦ (l, rewriteTyp ∅ mono t).
          rw [hInputs_fn] at hlt_mem
          obtain ⟨lt0, hlt0_mem, hlt0_eq⟩ := List.mem_map.mp hlt_mem
          subst hlt0_eq
          simp only
          -- Now goal: AppRefToDtOrNewDt (rewriteTyp ∅ mono lt0.2).
          have hAR : Typed.Typ.AppRefToDt tds [] lt0.2 :=
            hFnInInv fn_new hfn_new_mem lt0 hlt0_mem
          exact RefClosedBody.rewriteTyp_preserves_AppRefToDtOrNewDt hMonoShape hAR
        · -- output: md_f.output = rewriteTyp ∅ mono fn_new.output.
          rw [hOutput_fn]
          have hAR : Typed.Typ.AppRefToDt tds [] fn_new.output :=
            hFnOutInv fn_new hfn_new_mem
          exact RefClosedBody.rewriteTyp_preserves_AppRefToDtOrNewDt hMonoShape hAR
    -- h_cdAt_tds, h_cdAt_newDt — replicated from ctor arm verbatim.
    have h_cdAt_tds : ∀ g,
        (∃ dt, tds.getByKey g = some (.dataType dt) ∧ dt.params = []) →
        ∃ cdt, cd.getByKey g = some (.dataType cdt) := by
      intro g ⟨dt_orig, hdt_orig_get, hdt_params⟩
      have hg_in_cd : ∃ d, cd.getByKey g = some d := by
        have hinsert_pres : ∀ (acc : Typed.Decls) (k : Global) (v : Typed.Declaration),
            (∃ d, acc.getByKey g = some d) →
            ∃ d, (acc.insert k v).getByKey g = some d := by
          intro acc k v ⟨d, hget⟩
          by_cases hbeq : (k == g) = true
          · have hkeq : k = g := LawfulBEq.eq_of_beq hbeq
            rw [hkeq]; exact ⟨v, IndexMap.getByKey_insert_self _ _ _⟩
          · have hne : (k == g) = false := Bool.not_eq_true _ |>.mp hbeq
            exact ⟨d, by rw [IndexMap.getByKey_insert_of_beq_false _ _ hne]; exact hget⟩
        have hfn_pres : ∀ (acc : Typed.Decls) (f' : Typed.Function),
            (∃ d, acc.getByKey g = some d) →
            ∃ d, (PhaseA2.fnStep tds drained.mono acc f').getByKey g = some d := by
          intro acc f' hacc
          unfold PhaseA2.fnStep
          exact hinsert_pres acc _ _ hacc
        have hdt_inner_pres : ∀ (acc : Typed.Decls) (newDt' : DataType)
            (dt_outer : DataType) (cs : List Constructor),
            (∃ d, acc.getByKey g = some d) →
            ∃ d, (cs.foldl
              (fun acc'' c =>
                acc''.insert (dt_outer.name.pushNamespace c.nameHead)
                  (.constructor newDt' c)) acc).getByKey g = some d := by
          intro acc newDt' dt_outer cs hacc
          induction cs generalizing acc with
          | nil => exact hacc
          | cons c rest ih =>
            simp only [List.foldl_cons]
            apply ih
            exact hinsert_pres acc _ _ hacc
        have hdt_pres : ∀ (acc : Typed.Decls) (dt' : DataType),
            (∃ d, acc.getByKey g = some d) →
            ∃ d, (PhaseA2.dtStep drained.mono acc dt').getByKey g = some d := by
          intro acc dt' hacc
          simp only [PhaseA2.dtStep]
          apply hdt_inner_pres
          exact hinsert_pres acc _ _ hacc
        have hdt_list_fold_pres : ∀ (l : List DataType) (init : Typed.Decls),
            (∃ d, init.getByKey g = some d) →
            ∃ d, (l.foldl (PhaseA2.dtStep drained.mono) init).getByKey g = some d := by
          intro l
          induction l with
          | nil => intro init h; exact h
          | cons hd rest ih =>
            intro init h
            simp only [List.foldl_cons]
            exact ih _ (hdt_pres _ hd h)
        have hfn_list_fold_pres : ∀ (l : List Typed.Function) (init : Typed.Decls),
            (∃ d, init.getByKey g = some d) →
            ∃ d, (l.foldl (PhaseA2.fnStep tds drained.mono) init).getByKey g = some d := by
          intro l
          induction l with
          | nil => intro init h; exact h
          | cons hd rest ih =>
            intro init h
            simp only [List.foldl_cons]
            exact ih _ (hfn_pres _ hd h)
        have hmono_some : ∃ d, (concretizeBuild tds drained.mono drained.newFunctions
            drained.newDataTypes).getByKey g = some d := by
          rw [PhaseA2.concretizeBuild_eq]
          obtain ⟨md_dt, hsrc⟩ :=
            PhaseA2.fromSource_inserts_dataType_at_key tds drained.mono hdt_orig_get hdt_params
          have hsrc_ex : ∃ d, (tds.pairs.foldl (PhaseA2.srcStep tds drained.mono)
              default).getByKey g = some d := ⟨_, hsrc⟩
          rw [show (drained.newDataTypes.foldl (PhaseA2.dtStep drained.mono)
                (tds.pairs.foldl (PhaseA2.srcStep tds drained.mono) default))
              = (drained.newDataTypes.toList.foldl (PhaseA2.dtStep drained.mono)
                  (tds.pairs.foldl (PhaseA2.srcStep tds drained.mono) default))
              from by rw [← Array.foldl_toList]]
          rw [show (drained.newFunctions.foldl (PhaseA2.fnStep tds drained.mono) _)
              = (drained.newFunctions.toList.foldl (PhaseA2.fnStep tds drained.mono) _)
              from by rw [← Array.foldl_toList]]
          exact hfn_list_fold_pres _ _ (hdt_list_fold_pres _ _ hsrc_ex)
        obtain ⟨d_mono, hmono_get⟩ := hmono_some
        have h_kind := step4Lower_fold_kind_at_key hmono_get hconc'
        cases d_mono with
        | function _ => obtain ⟨cf, hcf⟩ := h_kind; exact ⟨_, hcf⟩
        | dataType _ => obtain ⟨cdt', hcdt'⟩ := h_kind; exact ⟨_, hcdt'⟩
        | constructor _ _ => obtain ⟨cdt', cc, hcc⟩ := h_kind; exact ⟨_, hcc⟩
      have hFnNotKey : ∀ f' ∈ drained.newFunctions, f'.name ≠ g := by
        intro f' hf' heq
        obtain ⟨g_f, args_f, f_orig, hf_name, hf_get, _hf_sz⟩ := hSNN.1 f' hf'
        have heq' : concretizeName g_f args_f = concretizeName g #[] := by
          rw [← hf_name, heq, concretizeName_empty_args]
        have hKey_in_cd : ∃ d, cd.getByKey (concretizeName g_f args_f) = some d := by
          rw [heq', concretizeName_empty_args]; exact hg_in_cd
        obtain ⟨hg_eq, _hargs_eq⟩ :=
          hUnique _hconc g_f g args_f #[] heq' hKey_in_cd
        rw [hg_eq] at hf_get
        rw [hdt_orig_get] at hf_get; cases hf_get
      have hDtCtorNotKey : ∀ dt' ∈ drained.newDataTypes, ∀ c ∈ dt'.constructors,
          dt'.name.pushNamespace c.nameHead ≠ g := by
        intro dt' hdt'_mem c hc heq
        let collisionArg : Typ := .ref ⟨.mkSimple c.nameHead⟩
        have hLHS_eq : concretizeName dt'.name #[collisionArg] =
            dt'.name.pushNamespace c.nameHead :=
          RefClosedBody.concretizeName_singleton_ref_simple dt'.name c.nameHead
        have heq_concName :
            concretizeName dt'.name #[collisionArg] = concretizeName g #[] := by
          rw [hLHS_eq, heq, concretizeName_empty_args]
        have hKey_in_cd' :
            ∃ d, cd.getByKey (concretizeName dt'.name #[collisionArg]) = some d := by
          rw [hLHS_eq, heq]; exact hg_in_cd
        obtain ⟨_hname_eq', hargs_witness⟩ :=
          hUnique _hconc dt'.name g #[collisionArg] #[] heq_concName hKey_in_cd'
        have hsz_lhs : (#[collisionArg] : Array Typ).size = 1 := rfl
        have hsz_rhs : (#[collisionArg] : Array Typ).size = 0 := by
          rw [hargs_witness]; rfl
        omega
      obtain ⟨md_dt, hmono_get⟩ :=
        PhaseA2.concretizeBuild_preserves_dataType_kind_fwd tds drained.mono
          drained.newFunctions drained.newDataTypes hdt_orig_get hdt_params
          hDtCtorNotKey hFnNotKey
      exact step4Lower_fold_dataType_bridge_inline hmono_get hconc'
    have h_cdAt_newDt : ∀ g,
        (∃ newDt ∈ drained.newDataTypes, newDt.name = g) →
        ∃ cdt, cd.getByKey g = some (.dataType cdt) := by
      intro g ⟨newDt, hnewDt_mem, hnewDt_name⟩
      rw [← hnewDt_name]
      obtain ⟨g_orig, args, dt_orig, hname_eq, hdt_orig_get, _hsz, _hctors⟩ :=
        hSNN.2 newDt hnewDt_mem
      have hg_in_cd : ∃ d, cd.getByKey newDt.name = some d :=
        RefClosedBody.cd_has_some_at_newDt_name hconc' hnewDt_mem
      have hFnNotKey : ∀ f' ∈ drained.newFunctions, f'.name ≠ newDt.name := by
        intro f' hf' heq
        obtain ⟨g_f, args_f, f_orig, hf_name, hf_get, _hf_sz⟩ := hSNN.1 f' hf'
        have heq' : concretizeName g_f args_f = concretizeName g_orig args := by
          rw [← hf_name, heq, hname_eq]
        have hKey_in_cd : ∃ d, cd.getByKey (concretizeName g_f args_f) = some d := by
          rw [heq', ← hname_eq]; exact hg_in_cd
        obtain ⟨hg_eq, _hargs_eq⟩ :=
          hUnique _hconc g_f g_orig args_f args heq' hKey_in_cd
        rw [hg_eq] at hf_get
        rw [hdt_orig_get] at hf_get; cases hf_get
      have hDtCtorNotKey : ∀ dt' ∈ drained.newDataTypes, ∀ c ∈ dt'.constructors,
          dt'.name.pushNamespace c.nameHead ≠ newDt.name := by
        intro dt' hdt'_mem c hc heq
        let collisionArg : Typ := .ref ⟨.mkSimple c.nameHead⟩
        have hLHS_eq : concretizeName dt'.name #[collisionArg] =
            dt'.name.pushNamespace c.nameHead :=
          RefClosedBody.concretizeName_singleton_ref_simple dt'.name c.nameHead
        have heq_concName :
            concretizeName dt'.name #[collisionArg] = concretizeName g_orig args := by
          rw [hLHS_eq, heq, hname_eq]
        have hKey_in_cd' :
            ∃ d, cd.getByKey (concretizeName dt'.name #[collisionArg]) = some d := by
          rw [hLHS_eq, heq]; exact hg_in_cd
        obtain ⟨hname_dt'_eq, hargs_witness⟩ :=
          hUnique _hconc dt'.name g_orig #[collisionArg] args heq_concName hKey_in_cd'
        have hsz_args : args.size = 1 := by rw [← hargs_witness]; rfl
        obtain ⟨g'_orig, args'_dt, dt'_orig, hdt'_name, hdt'_get, hdt'_sz, _⟩ :=
          hSNN.2 dt' hdt'_mem
        have heq2 : concretizeName g'_orig args'_dt = concretizeName g_orig #[] := by
          rw [← hdt'_name, hname_dt'_eq, concretizeName_empty_args]
        have hKey2 : ∃ d, cd.getByKey (concretizeName g'_orig args'_dt) = some d := by
          rw [← hdt'_name]
          exact RefClosedBody.cd_has_some_at_newDt_name hconc' hdt'_mem
        obtain ⟨_hg'_eq, hargs'_eq⟩ :=
          hUnique _hconc g'_orig g_orig args'_dt #[] heq2 hKey2
        have hargs'_size : args'_dt.size = 0 := by rw [hargs'_eq]; rfl
        rw [hargs'_size] at hdt'_sz
        rw [_hg'_eq, hdt_orig_get] at hdt'_get
        have hdt_orig_eq : dt'_orig = dt_orig := by
          have h1 : (Typed.Declaration.dataType dt_orig) =
              .dataType dt'_orig := Option.some.inj hdt'_get
          injection h1.symm
        rw [hdt_orig_eq] at hdt'_sz
        rw [hsz_args] at _hsz
        omega
      obtain ⟨md_dt, hmono_get⟩ :=
        PhaseA2.concretizeBuild_at_newDt_name tds drained.mono drained.newFunctions
          drained.newDataTypes hnewDt_mem hDtCtorNotKey hFnNotKey
      exact step4Lower_fold_dataType_bridge_inline hmono_get hconc'
    have h_cdMono_dt : ∀ (g : Global) (args : Array Typ) (concName : Global),
        (∃ dt, tds.getByKey g = some (.dataType dt)) →
        (∅ : Std.HashMap (Global × Array Typ) Global)[(g, args)]? = some concName →
        ∃ cdt, cd.getByKey concName = some (.dataType cdt) := by
      intro g args concName _ hsome
      simp at hsome
    obtain ⟨h_md_AR_inputs, h_md_AR_output⟩ := h_md_AR_combined
    -- Closure 2026-04-30: per-element apps-coverage via the new
    -- `function_arm_no_app_md_f` helper (uses `AppsReachedCond` post-drain
    -- + `SeenSubsetMono` + origin-split; no `FullyMonomorphic`).
    have hcd_at_name : ∃ d, cd.getByKey name = some d := ⟨_, hcd_get_full⟩
    obtain ⟨h_md_appCov_inputs, h_md_appCov_output⟩ :=
      function_arm_no_app_md_f _hwf _hdecls _hts hdrain hSSM hARC hPE hmd_get
        hMonoShape hNFFS hUnique hSNN _hconc hcd_at_name
    have h_inputs : ∀ lt ∈ f.inputs, Concrete.Typ.RefClosed cd lt.snd := by
      intro lt hlt
      refine List.mem_mapM_ok_forall
        (P := fun (p : Local × Typ) =>
          RefClosedBody.Typed.Typ.AppRefToDtOrNewDt tds drained.newDataTypes p.2 ∧
          (∀ g args (mono : MonoMap),
            RefClosedBody.Typ.containsApp g args p.2 →
            ∃ concName, mono[(g, args)]? = some concName))
        (Q := fun (p : Local × Concrete.Typ) =>
          Concrete.Typ.RefClosed cd p.2)
        ?_ md_f.inputs f.inputs ?_ hinputs_witness lt hlt
      · intro p ⟨hp_AR, hp_appCov⟩ fx hfx
        simp only [bind, Except.bind, pure, Except.pure] at hfx
        split at hfx
        · cases hfx
        rename_i t' hconc_t'
        cases hfx
        exact RefClosedBody.typToConcrete_RefClosed_via_AppRefToDtOrNewDt
          (mono := ∅) h_cdAt_tds h_cdAt_newDt h_cdMono_dt hp_AR
          (hp_appCov · · ∅) hconc_t'
      · intro p hp
        refine ⟨h_md_AR_inputs p.2 (List.mem_map_of_mem hp), ?_⟩
        exact h_md_appCov_inputs p hp
    have h_output : Concrete.Typ.RefClosed cd f.output :=
      RefClosedBody.typToConcrete_RefClosed_via_AppRefToDtOrNewDt
        (mono := ∅) h_cdAt_tds h_cdAt_newDt h_cdMono_dt h_md_AR_output
        (h_md_appCov_output · · ∅) houtput_witness
    exact ⟨h_inputs, h_output⟩
  | .dataType dt, hget =>
    -- Sub-claim A.1-dt: every t in every constructor's argTypes is RefClosed cd.
    -- Mirrors .ctor arm but at the dataType level. Uses
    -- `step4Lower_dataType_explicit` (from Shapes.lean) for the per-ctor mapM
    -- witness, and `DirectDagBody.concretizeBuild_dataType_origin` (from CtorKind.lean)
    -- for the source-vs-newDt origin split.
    have h_dt : ∀ c ∈ dt.constructors, ∀ t ∈ c.argTypes,
        Concrete.Typ.RefClosed cd t := by
      have hconc' := _hconc
      unfold Typed.Decls.concretize at hconc'
      simp only [bind, Except.bind] at hconc'
      split at hconc'
      · cases hconc'
      rename_i drained hdrain
      have hSNN : drained.StrongNewNameShape tds :=
        concretize_drain_preserves_StrongNewNameShape _ _
          (DrainState.StrongNewNameShape.init tds (concretizeSeed tds)) hdrain
      have hMonoShape : drained.MonoShapeOk tds :=
        concretize_drain_shape_equation _ _
          (DrainState.MonoShapeOk.init tds (concretizeSeed tds)) hdrain
      have hNDFS : drained.NewDtFullShape tds :=
        concretize_drain_preserves_NewDtFullShape _ _
          (DrainState.NewDtFullShape.init tds (concretizeSeed tds)) hdrain
      have hUnique : Typed.Decls.ConcretizeUniqueNames tds :=
        _hwf.noNameCollisions _ _hts
      have hSSM : drained.SeenSubsetMono :=
        concretize_drain_preserves_SeenSubsetMono _ _
          (DrainState.SeenSubsetMono.init _) hdrain
      have hARC : drained.AppsReachedCond tds :=
        concretize_drain_preserves_AppsReachedCond _ _
          (DrainState.AppsReachedCond.init tds) hdrain
      have hPE_b : drained.pending.isEmpty :=
        concretize_drain_succeeds_pending_empty _ _ hdrain
      have hPE : ∀ q, q ∈ drained.pending → False := by
        intro q hq
        have hne : drained.pending.isEmpty = false := by
          rw [Std.HashSet.isEmpty_eq_false_iff_exists_contains_eq_true]
          exact ⟨q, Std.HashSet.contains_iff_mem.mpr hq⟩
        rw [hne] at hPE_b; cases hPE_b
      -- Backward: monoDecls has .dataType at name.
      obtain ⟨md_dt, hmd_get⟩ :=
        step4Lower_backward_dataType_kind_at_key hget hconc'
      -- step4Lower forward: cdt' = dt + ctors mapM witness.
      obtain ⟨cd_dt', hcd_get_full, _hname_eq, hLen, hPosNH, hctors_witness⟩ :=
        step4Lower_dataType_explicit hmd_get hconc'
      -- Identify cd_dt' = dt via hget vs hcd_get_full.
      have hsame : (Concrete.Declaration.dataType cd_dt') =
          .dataType dt := by
        rw [hcd_get_full] at hget; exact (Option.some.injEq _ _).mp hget
      have heq_dt : cd_dt' = dt := by injection hsame
      rw [heq_dt] at hLen hPosNH hctors_witness
      -- AppRefToDtOrNewDt for every elt in every md_dt.constructors[i].argTypes.
      -- Origin split on md_dt via concretizeBuild_dataType_origin:
      -- (A) source case: tds .dataType at name with src_dt.params=[]; md_dt
      --     ctors are src_dt.constructors mapped via rewriteTyp ∅ drained.mono.
      -- (B) newDt case: dt' ∈ drained.newDataTypes with dt'.name = name;
      --     md_dt ctors come from drain via dtStep — use CtorArgsAppRefToDt.
      have h_md_AR : ∀ md_c ∈ md_dt.constructors, ∀ t' ∈ md_c.argTypes,
          RefClosedBody.Typed.Typ.AppRefToDtOrNewDt tds drained.newDataTypes t' := by
        rcases DirectDagBody.concretizeBuild_dataType_origin tds drained.mono
            drained.newFunctions drained.newDataTypes hmd_get with
          ⟨src_dt, hsrc_get, hsrc_params⟩ | ⟨dt_new, hdt_new_mem, hdt_new_name⟩
        · -- (A) source case.
          have hcd_at_name : ∃ d, cd.getByKey name = some d := ⟨_, hcd_get_full⟩
          have hFnNotKey : ∀ f ∈ drained.newFunctions, f.name ≠ name := by
            intro f hmem heq
            obtain ⟨g_orig, args, f_orig, hname_eq', hf_get, _⟩ := hSNN.1 f hmem
            have heq' : concretizeName g_orig args = concretizeName name #[] := by
              rw [← hname_eq', heq, concretizeName_empty_args]
            have hKey : ∃ d, cd.getByKey (concretizeName g_orig args) = some d := by
              rw [heq', concretizeName_empty_args]; exact hcd_at_name
            obtain ⟨hg_eq, _⟩ := hUnique _hconc g_orig name args #[] heq' hKey
            -- tds has .function at g_orig and .dataType at name = g_orig.
            rw [hg_eq] at hf_get
            rw [hsrc_get] at hf_get
            cases hf_get
          have hCtorNotKey : ∀ dt' ∈ drained.newDataTypes, ∀ c ∈ dt'.constructors,
              dt'.name.pushNamespace c.nameHead ≠ name := by
            intro dt' hmem c hc heq
            let collisionArg : Typ := .ref ⟨.mkSimple c.nameHead⟩
            have hLHS_eq : concretizeName dt'.name #[collisionArg] =
                dt'.name.pushNamespace c.nameHead :=
              RefClosedBody.concretizeName_singleton_ref_simple dt'.name c.nameHead
            have heq_concName :
                concretizeName dt'.name #[collisionArg] = concretizeName name #[] := by
              rw [hLHS_eq, heq, concretizeName_empty_args]
            have hKey : ∃ d, cd.getByKey (concretizeName dt'.name #[collisionArg]) = some d := by
              rw [hLHS_eq, heq]; exact hcd_at_name
            obtain ⟨_, hargs_eq⟩ :=
              hUnique _hconc dt'.name name #[collisionArg] #[] heq_concName hKey
            have h1 : (#[collisionArg] : Array Typ).size = 1 := rfl
            have h0 : (#[collisionArg] : Array Typ).size = 0 := by rw [hargs_eq]; rfl
            omega
          -- Drain MAY emit a newDt at `name` (when collectCalls picks up a
          -- monomorphic ref to `name` in some body/type). In that case, dtStep
          -- overrides srcStep's insert at `name`. We case-split. The shared
          -- conclusion in both branches is `md_dt.constructors = rewrittenCtors`,
          -- which is sufficient to discharge the per-ctor AR-claim downstream.
          let rewrittenCtors : List Constructor := src_dt.constructors.map fun c =>
            { c with argTypes := c.argTypes.map (rewriteTyp (fun _ => none) drained.mono) }
          have hmd_dt_ctors : md_dt.constructors = rewrittenCtors := by
            by_cases hOverride : ∃ dt' ∈ drained.newDataTypes, dt'.name = name
            · -- Override sub-case: identify md_dt.constructors via the newDt explicit form.
              obtain ⟨dt', hdt'_mem, hdt'_name⟩ := hOverride
              -- Use FullShape to identify dt' in terms of src_dt.
              obtain ⟨g_orig, args, dt_orig, _hin_seen, hdt_orig_get, hsz, hdt'_shape⟩ :=
                hNDFS dt' hdt'_mem
              have hdt'_name' : dt'.name = concretizeName g_orig args := by
                rw [hdt'_shape]
              have heq' : concretizeName g_orig args = concretizeName name #[] := by
                rw [← hdt'_name', hdt'_name, concretizeName_empty_args]
              have hKey : ∃ d, cd.getByKey (concretizeName g_orig args) = some d := by
                rw [heq', concretizeName_empty_args]; exact hcd_at_name
              obtain ⟨hg_eq, hargs_eq⟩ :=
                hUnique _hconc g_orig name args #[] heq' hKey
              -- Establish dt_orig = src_dt via tds value uniqueness at name.
              rw [hg_eq] at hdt_orig_get
              rw [hsrc_get] at hdt_orig_get
              have hdt_orig_eq : dt_orig = src_dt := by
                have h1 : Typed.Declaration.dataType src_dt = .dataType dt_orig :=
                  Option.some.inj hdt_orig_get
                injection h1.symm
              have hsubst_empty : mkParamSubst dt_orig.params args = fun _ => none := by
                rw [hdt_orig_eq, hsrc_params, hargs_eq]
                funext g; simp [mkParamSubst]
              -- Apply override-aware explicit lemma.
              have hOtherDtNotKey : ∀ dt'' ∈ drained.newDataTypes, dt'' ≠ dt' →
                  dt''.name ≠ dt'.name := by
                intro dt'' hdt''_mem hne heq2
                obtain ⟨g2, args2, dt_orig2, _, hdt_orig2_get, _, hdt''_shape⟩ :=
                  hNDFS dt'' hdt''_mem
                obtain ⟨g1, args1, dt_orig1, _, hdt_orig1_get, _, hdt'_shape'⟩ :=
                  hNDFS dt' hdt'_mem
                have hname_dt'' : dt''.name = concretizeName g2 args2 := by
                  rw [hdt''_shape]
                have hname_dt' : dt'.name = concretizeName g1 args1 := by
                  rw [hdt'_shape']
                have heq1 : concretizeName g2 args2 = concretizeName g1 args1 := by
                  rw [← hname_dt'', heq2, hname_dt']
                have hKey1 : ∃ d, cd.getByKey (concretizeName g2 args2) = some d := by
                  rw [heq1, ← hname_dt', hdt'_name]; exact hcd_at_name
                obtain ⟨hg_eq', hargs_eq'⟩ :=
                  hUnique _hconc g2 g1 args2 args1 heq1 hKey1
                rw [hg_eq'] at hdt_orig2_get
                rw [hdt_orig1_get] at hdt_orig2_get
                have hdt_orig_eq' : dt_orig2 = dt_orig1 := by
                  have h1 : Typed.Declaration.dataType dt_orig1 =
                      .dataType dt_orig2 := Option.some.inj hdt_orig2_get
                  injection h1.symm
                apply hne
                rw [hdt''_shape, hdt'_shape', hg_eq', hargs_eq', hdt_orig_eq']
              have hDtCtorNotKey : ∀ dt'' ∈ drained.newDataTypes, ∀ c ∈ dt''.constructors,
                  dt''.name.pushNamespace c.nameHead ≠ dt'.name := by
                intro dt'' hdt''_mem c hc heq2
                rw [hdt'_name] at heq2
                exact hCtorNotKey dt'' hdt''_mem c hc heq2
              have hFnNotKey' : ∀ f ∈ drained.newFunctions, f.name ≠ dt'.name := by
                intro f hf_mem hfeq
                rw [hdt'_name] at hfeq
                exact hFnNotKey f hf_mem hfeq
              obtain ⟨md_dt_at, hmd_at_get_dt, _hName_dt, _hParams_dt, hCtors_dt⟩ :=
                PhaseA2.concretizeBuild_at_newDt_name_full_explicit tds drained.mono
                  drained.newFunctions drained.newDataTypes hdt'_mem
                  hDtCtorNotKey hFnNotKey' hOtherDtNotKey
              rw [hdt'_name] at hmd_at_get_dt
              rw [hmd_at_get_dt] at hmd_get
              have hmd_eq : md_dt_at = md_dt := by
                have h1 : Typed.Declaration.dataType md_dt_at = .dataType md_dt :=
                  Option.some.inj hmd_get
                injection h1
              rw [hmd_eq] at hCtors_dt
              -- hCtors_dt : md_dt.constructors = dt'.constructors.map (...).
              -- Translate dt'.constructors via NewDtFullShape + empty-subst collapse.
              have hdt'_ctors_proj : dt'.constructors =
                  dt_orig.constructors.map (fun c =>
                    ({ c with argTypes :=
                      c.argTypes.map (Typ.instantiate (mkParamSubst dt_orig.params args)) }
                      : Constructor)) := by
                rw [hdt'_shape]
              have hdt'_ctors_id : dt'.constructors = src_dt.constructors := by
                rw [hdt'_ctors_proj, hsubst_empty, hdt_orig_eq]
                induction src_dt.constructors with
                | nil => rfl
                | cons hd tl ih =>
                  have hat_eq : hd.argTypes.map (Typ.instantiate (fun _ => none))
                      = hd.argTypes := by
                    induction hd.argTypes with
                    | nil => rfl
                    | cons hd' tl' ih' =>
                      show Typ.instantiate (fun _ => none) hd' :: tl'.map _ = hd' :: tl'
                      rw [Typ.instantiate_empty_id, ih']
                  show ({ hd with argTypes :=
                          hd.argTypes.map (Typ.instantiate (fun _ => none)) } : Constructor)
                      :: tl.map _ = hd :: tl
                  rw [hat_eq, ih]
              -- Now md_dt.constructors = dt'.constructors.map ... = src_dt.constructors.map ... = rewrittenCtors.
              show md_dt.constructors = rewrittenCtors
              rw [hCtors_dt, hdt'_ctors_id]
            · -- No-override sub-case: existing source-mono path via hDtNotKey.
              have hDtNotKey : ∀ dt' ∈ drained.newDataTypes, dt'.name ≠ name := by
                intro dt' hmem heq2
                exact hOverride ⟨dt', hmem, heq2⟩
              have hexplicit :=
                PhaseA2.concretizeBuild_at_typed_dataType_explicit tds drained.mono
                  drained.newFunctions drained.newDataTypes hsrc_get hsrc_params
                  hDtNotKey hFnNotKey hCtorNotKey
              rw [hexplicit] at hmd_get
              -- hmd_get gives the explicit monoDt-shape; extract md_dt.constructors.
              have h1 : Typed.Declaration.dataType
                ({ src_dt with constructors := rewrittenCtors } : DataType) =
                .dataType md_dt := Option.some.inj hmd_get
              have h2 : ({ src_dt with constructors := rewrittenCtors } : DataType) = md_dt := by
                injection h1
              show md_dt.constructors = rewrittenCtors
              rw [← h2]
          -- Now goal: ∀ md_c ∈ monoDt.constructors, ∀ t' ∈ md_c.argTypes, AppRefToDtOrNewDt.
          -- Source-side wellFormedness for src_dt.
          have hP := FnMatchP_checkAndSimplify _hdecls _hts
          have hsrc_decl_dt : decls.getByKey name = some (.dataType src_dt) :=
            (hP name).2.1 src_dt hsrc_get
          have hwf := checkAndSimplify_implies_wellFormedDecls _hdecls _hts
          have hsrc_dt_pair :
              (name, Source.Declaration.dataType src_dt) ∈ decls.pairs.toList :=
            IndexMap.mem_pairs_of_getByKey _ _ _ hsrc_decl_dt
          have hdt_key_name := mkDecls_dt_key_is_name _hdecls
          obtain ⟨vis, vis', hvis_fresh, hwf_dt⟩ :=
            wellFormedDecls_reflect_dataType_fresh hdt_key_name hwf hsrc_dt_pair
          have hwf_argtypes := wellFormedDecls_reflect_dataType hvis_fresh hwf_dt
          -- Lift wellFormedness to AppRefToDtOrNewDt.
          have h_dt_lift : ∀ g, (∃ dt_src, decls.getByKey g = some (.dataType dt_src)) →
              ∃ dt_td, tds.getByKey g = some (.dataType dt_td) := by
            intro g ⟨dt_src, hget_src⟩
            obtain ⟨dt_td, hget_td⟩ := checkAndSimplify_src_dt_to_td _hdecls _hts hget_src
            exact ⟨dt_td, hget_td⟩
          have h_dt_params_lift : ∀ g,
              (∃ dt_src, decls.getByKey g = some (.dataType dt_src) ∧ dt_src.params = []) →
              ∃ dt_td, tds.getByKey g = some (.dataType dt_td) ∧ dt_td.params = [] := by
            intro g ⟨dt_src, hget_src, hparams⟩
            obtain ⟨dt_td, hget_td⟩ := checkAndSimplify_src_dt_to_td _hdecls _hts hget_src
            have hsrc' : decls.getByKey g = some (.dataType dt_td) := (hP g).2.1 dt_td hget_td
            have h1 : Source.Declaration.dataType dt_src = .dataType dt_td := by
              rw [hget_src] at hsrc'
              exact Option.some.inj hsrc'
            have hdt_eq : dt_src = dt_td := by injection h1
            exact ⟨dt_td, hget_td, hdt_eq ▸ hparams⟩
          -- Per-ctor: monoDt.constructors[i] has argTypes derived from src_dt.constructors[i].argTypes
          -- via rewriteTyp ∅ drained.mono.
          intro md_c hmd_c_mem t' ht'_mem
          -- md_c ∈ rewrittenCtors. Find src_c in src_dt.constructors with rewritten args matching md_c.
          show RefClosedBody.Typed.Typ.AppRefToDtOrNewDt tds drained.newDataTypes t'
          rw [hmd_dt_ctors] at hmd_c_mem
          have hmc_in_rew : md_c ∈ rewrittenCtors := hmd_c_mem
          obtain ⟨src_c, hsrc_c_mem, hsrc_c_eq⟩ := List.mem_map.mp hmc_in_rew
          -- md_c.argTypes = src_c.argTypes.map (rewriteTyp ∅ drained.mono).
          have hmc_at : md_c.argTypes =
              src_c.argTypes.map (rewriteTyp (fun _ => none) drained.mono) := by
            rw [← hsrc_c_eq]
          rw [hmc_at] at ht'_mem
          obtain ⟨src_t, hsrc_t_mem, ht'_eq⟩ := List.mem_map.mp ht'_mem
          subst ht'_eq
          -- src_c ∈ src_dt.constructors. Wellformedness-of-dataType gives wellformedType per arg.
          have hwf_t : wellFormedDecls.wellFormedType decls src_dt.params src_t = .ok () :=
            hwf_argtypes src_c hsrc_c_mem src_t hsrc_t_mem
          rw [hsrc_params] at hwf_t
          have hSRD := SrcTypRefsAreDtKeys_of_wellFormedType decls [] src_t hwf_t
          have hAR := RefClosedBody.AppRefToDt_of_SrcTypRefsAreDtKeys
            h_dt_lift h_dt_params_lift hSRD
          exact RefClosedBody.rewriteTyp_preserves_AppRefToDtOrNewDt hMonoShape hAR
        · -- (B) newDt case: dt_new ∈ drained.newDataTypes with dt_new.name = name.
          -- md_dt comes from dtStep applied to dt_new, so md_dt.constructors are
          -- dt_new.constructors with argTypes rewritten via rewriteTyp ∅ drained.mono.
          -- Apply `concretizeBuild_at_newDt_name_explicit` to identify md_dt.
          have hcd_at_name : ∃ d, cd.getByKey name = some d := ⟨_, hcd_get_full⟩
          rw [← hdt_new_name] at hmd_get hcd_at_name
          -- Disjointness premises for the explicit lemma.
          have hFnNotKey : ∀ f ∈ drained.newFunctions, f.name ≠ dt_new.name := by
            intro f hmem heq
            obtain ⟨g_orig, args, f_orig, hname_eq', hf_get, _⟩ := hSNN.1 f hmem
            obtain ⟨g_new_orig, args_new, dt_new_orig, hname_eq_new, hdt_new_get, _, _⟩ :=
              hSNN.2 dt_new hdt_new_mem
            have heq1 : concretizeName g_orig args = concretizeName g_new_orig args_new := by
              rw [← hname_eq', heq, hname_eq_new]
            have hKey1 : ∃ d, cd.getByKey (concretizeName g_orig args) = some d := by
              rw [heq1, ← hname_eq_new]; exact hcd_at_name
            obtain ⟨hg_eq, _⟩ := hUnique _hconc g_orig g_new_orig args args_new heq1 hKey1
            rw [hg_eq] at hf_get
            rw [hdt_new_get] at hf_get
            cases hf_get
          have hDtCtorNotKey : ∀ dt' ∈ drained.newDataTypes, ∀ c ∈ dt'.constructors,
              dt'.name.pushNamespace c.nameHead ≠ dt_new.name := by
            intro dt' hdt'_mem c hc heq
            let collisionArg : Typ := .ref ⟨.mkSimple c.nameHead⟩
            have hLHS_eq : concretizeName dt'.name #[collisionArg] =
                dt'.name.pushNamespace c.nameHead :=
              RefClosedBody.concretizeName_singleton_ref_simple dt'.name c.nameHead
            obtain ⟨g_orig, args, dt_orig, hname_eq', hdt_orig_get, hsz', _⟩ :=
              hSNN.2 dt' hdt'_mem
            obtain ⟨g_new_orig, args_new, dt_new_orig, hname_eq_new, hdt_new_get,
                    hsz_new, _⟩ := hSNN.2 dt_new hdt_new_mem
            -- heq : dt'.name.pushNamespace c.nameHead = dt_new.name.
            -- This is exactly the standard pattern in h_cdAt_newDt's ctor arm:
            -- after hUnique on (dt'.name, #[collisionArg]) vs (g_new_orig, args_new),
            -- we get args_new.size = 1, conflicting with the dt_new SNN witness.
            have heq_concName : concretizeName dt'.name #[collisionArg] =
                concretizeName g_new_orig args_new := by
              rw [hLHS_eq, heq, hname_eq_new]
            have hKey1 : ∃ d, cd.getByKey
                (concretizeName dt'.name #[collisionArg]) = some d := by
              rw [hLHS_eq, heq]; exact hcd_at_name
            obtain ⟨hname_dt'_eq, hargs_witness⟩ :=
              hUnique _hconc dt'.name g_new_orig #[collisionArg] args_new heq_concName hKey1
            have hsz_args : args_new.size = 1 := by rw [← hargs_witness]; rfl
            obtain ⟨g'_orig, args'_dt, dt'_orig, hdt'_name, hdt'_get, hdt'_sz, _⟩ :=
              hSNN.2 dt' hdt'_mem
            have heq2 : concretizeName g'_orig args'_dt = concretizeName g_new_orig #[] := by
              rw [← hdt'_name, hname_dt'_eq, concretizeName_empty_args]
            have hKey2 : ∃ d, cd.getByKey (concretizeName g'_orig args'_dt) = some d := by
              rw [← hdt'_name]
              exact RefClosedBody.cd_has_some_at_newDt_name hconc' hdt'_mem
            obtain ⟨_hg'_eq, hargs'_eq⟩ :=
              hUnique _hconc g'_orig g_new_orig args'_dt #[] heq2 hKey2
            have hargs'_size : args'_dt.size = 0 := by rw [hargs'_eq]; rfl
            rw [hargs'_size] at hdt'_sz
            -- dt'_orig at g'_orig = dt_new_orig at g_new_orig (same tds key).
            rw [_hg'_eq, hdt_new_get] at hdt'_get
            have hdt_orig_eq : dt'_orig = dt_new_orig := by
              have h1 : (Typed.Declaration.dataType dt_new_orig) =
                  .dataType dt'_orig := Option.some.inj hdt'_get
              injection h1.symm
            rw [hdt_orig_eq] at hdt'_sz
            -- args_new.size = 1 (from hsz_args), but dt_new_orig.params.length = args'_dt.size = 0.
            -- Combined with hsz_new : args_new.size = dt_new_orig.params.length = 0.
            rw [hsz_args] at hsz_new
            omega
          have hOtherDtNotKey : ∀ dt' ∈ drained.newDataTypes, dt' ≠ dt_new →
              dt'.name ≠ dt_new.name := by
            intro dt' hdt'_mem hne heq
            -- FullShape gives canonical push origin for both dts.
            obtain ⟨g_orig, args, dt_orig, _, hdt_orig_get, _, hshape⟩ :=
              hNDFS dt' hdt'_mem
            obtain ⟨g_new_orig, args_new, dt_new_orig, _, hdt_new_get, _, hshape_new⟩ :=
              hNDFS dt_new hdt_new_mem
            -- Names: dt'.name = cN g_orig args, dt_new.name = cN g_new_orig args_new.
            have hname_dt' : dt'.name = concretizeName g_orig args := by
              rw [hshape]
            have hname_dtn : dt_new.name = concretizeName g_new_orig args_new := by
              rw [hshape_new]
            have heq1 : concretizeName g_orig args =
                concretizeName g_new_orig args_new := by
              rw [← hname_dt', heq, hname_dtn]
            -- cd-key witness via dt' ∈ newDataTypes.
            have hKey1 : ∃ d, cd.getByKey (concretizeName g_orig args) = some d := by
              rw [← hname_dt']
              exact RefClosedBody.cd_has_some_at_newDt_name hconc' hdt'_mem
            obtain ⟨hg_eq, hargs_eq⟩ :=
              hUnique _hconc g_orig g_new_orig args args_new heq1 hKey1
            -- dt_orig = dt_new_orig (same tds key g_orig = g_new_orig).
            rw [hg_eq] at hdt_orig_get
            rw [hdt_new_get] at hdt_orig_get
            have hdt_orig_eq : dt_orig = dt_new_orig := by
              have h1 : Typed.Declaration.dataType dt_new_orig =
                  .dataType dt_orig := Option.some.inj hdt_orig_get
              injection h1.symm
            -- Both dt' and dt_new equal the canonical push shape for the same
            -- (g, args, dt_orig) — hence dt' = dt_new, contradicting hne.
            apply hne
            rw [hshape, hshape_new, hg_eq, hargs_eq, hdt_orig_eq]
          obtain ⟨md_dt_at, hmd_at_get_dt, hName_dt, _hParams_dt, hCtors_dt⟩ :=
            PhaseA2.concretizeBuild_at_newDt_name_full_explicit tds drained.mono
              drained.newFunctions drained.newDataTypes hdt_new_mem
              hDtCtorNotKey hFnNotKey hOtherDtNotKey
          rw [hmd_at_get_dt] at hmd_get
          have hmd_eq : md_dt_at = md_dt := by
            have h1 : Typed.Declaration.dataType md_dt_at = .dataType md_dt :=
              Option.some.inj hmd_get
            injection h1
          rw [hmd_eq] at hCtors_dt hName_dt
          -- Direct closure via the FULL structural witness:
          -- md_dt.constructors = dt_new.constructors.map (rewriteTyp ∅ drained.mono).
          -- Each md_c ∈ md_dt.constructors comes from some c0 ∈ dt_new.constructors;
          -- md_c.argTypes = c0.argTypes.map (rewriteTyp ∅ drained.mono).
          -- c0 ∈ dt_new ⊂ newDataTypes ⟹ c0.argTypes are AppRefToDt-safe via
          -- CtorArgsAppRefToDt drain invariant.
          -- rewriteTyp_preserves_AppRefToDtOrNewDt lifts to AppRefToDtOrNewDt.
          have hCAR_invariant : drained.CtorArgsAppRefToDt tds :=
            concretize_produces_CtorArgsAppRefToDt _hwf _hdecls _hts hdrain
          intro md_c hmd_c_mem t' ht'_mem
          rw [hCtors_dt] at hmd_c_mem
          obtain ⟨c0, hc0_mem, hc0_eq⟩ := List.mem_map.mp hmd_c_mem
          -- md_c = { c0 with argTypes := c0.argTypes.map (rewriteTyp ∅ drained.mono) }.
          have hat_eq : md_c.argTypes =
              c0.argTypes.map (rewriteTyp (fun _ => none) drained.mono) := by
            rw [← hc0_eq]
          rw [hat_eq] at ht'_mem
          obtain ⟨src_t, hsrc_t_mem, ht'_eq⟩ := List.mem_map.mp ht'_mem
          subst ht'_eq
          have hAR : Typed.Typ.AppRefToDt tds [] src_t :=
            hCAR_invariant dt_new hdt_new_mem c0 hc0_mem src_t hsrc_t_mem
          exact RefClosedBody.rewriteTyp_preserves_AppRefToDtOrNewDt hMonoShape hAR
      -- h_cdAt_tds, h_cdAt_newDt, h_cdMono_dt — replicate from .ctor arm verbatim.
      have h_cdAt_tds : ∀ g,
          (∃ dt, tds.getByKey g = some (.dataType dt) ∧ dt.params = []) →
          ∃ cdt, cd.getByKey g = some (.dataType cdt) := by
        intro g ⟨dt_orig, hdt_orig_get, hdt_params⟩
        have hg_in_cd : ∃ d, cd.getByKey g = some d := by
          have hinsert_pres : ∀ (acc : Typed.Decls) (k : Global) (v : Typed.Declaration),
              (∃ d, acc.getByKey g = some d) →
              ∃ d, (acc.insert k v).getByKey g = some d := by
            intro acc k v ⟨d, hget'⟩
            by_cases hbeq : (k == g) = true
            · have hkeq : k = g := LawfulBEq.eq_of_beq hbeq
              rw [hkeq]; exact ⟨v, IndexMap.getByKey_insert_self _ _ _⟩
            · have hne : (k == g) = false := Bool.not_eq_true _ |>.mp hbeq
              exact ⟨d, by rw [IndexMap.getByKey_insert_of_beq_false _ _ hne]; exact hget'⟩
          have hfn_pres : ∀ (acc : Typed.Decls) (f : Typed.Function),
              (∃ d, acc.getByKey g = some d) →
              ∃ d, (PhaseA2.fnStep tds drained.mono acc f).getByKey g = some d := by
            intro acc f hacc
            unfold PhaseA2.fnStep
            exact hinsert_pres acc _ _ hacc
          have hdt_inner_pres : ∀ (acc : Typed.Decls) (newDt' : DataType)
              (dt_outer : DataType) (cs : List Constructor),
              (∃ d, acc.getByKey g = some d) →
              ∃ d, (cs.foldl
                (fun acc'' c =>
                  acc''.insert (dt_outer.name.pushNamespace c.nameHead)
                    (.constructor newDt' c)) acc).getByKey g = some d := by
            intro acc newDt' dt_outer cs hacc
            induction cs generalizing acc with
            | nil => exact hacc
            | cons c rest ih =>
              simp only [List.foldl_cons]
              apply ih
              exact hinsert_pres acc _ _ hacc
          have hdt_pres : ∀ (acc : Typed.Decls) (dt' : DataType),
              (∃ d, acc.getByKey g = some d) →
              ∃ d, (PhaseA2.dtStep drained.mono acc dt').getByKey g = some d := by
            intro acc dt' hacc
            simp only [PhaseA2.dtStep]
            apply hdt_inner_pres
            exact hinsert_pres acc _ _ hacc
          have hdt_list_fold_pres : ∀ (l : List DataType) (init : Typed.Decls),
              (∃ d, init.getByKey g = some d) →
              ∃ d, (l.foldl (PhaseA2.dtStep drained.mono) init).getByKey g = some d := by
            intro l
            induction l with
            | nil => intro init h; exact h
            | cons hd rest ih =>
              intro init h
              simp only [List.foldl_cons]
              exact ih _ (hdt_pres _ hd h)
          have hfn_list_fold_pres : ∀ (l : List Typed.Function) (init : Typed.Decls),
              (∃ d, init.getByKey g = some d) →
              ∃ d, (l.foldl (PhaseA2.fnStep tds drained.mono) init).getByKey g = some d := by
            intro l
            induction l with
            | nil => intro init h; exact h
            | cons hd rest ih =>
              intro init h
              simp only [List.foldl_cons]
              exact ih _ (hfn_pres _ hd h)
          have hmono_some : ∃ d, (concretizeBuild tds drained.mono drained.newFunctions
              drained.newDataTypes).getByKey g = some d := by
            rw [PhaseA2.concretizeBuild_eq]
            obtain ⟨md_dt', hsrc⟩ :=
              PhaseA2.fromSource_inserts_dataType_at_key tds drained.mono hdt_orig_get hdt_params
            have hsrc_ex : ∃ d, (tds.pairs.foldl (PhaseA2.srcStep tds drained.mono)
                default).getByKey g = some d := ⟨_, hsrc⟩
            rw [show (drained.newDataTypes.foldl (PhaseA2.dtStep drained.mono)
                  (tds.pairs.foldl (PhaseA2.srcStep tds drained.mono) default))
                = (drained.newDataTypes.toList.foldl (PhaseA2.dtStep drained.mono)
                    (tds.pairs.foldl (PhaseA2.srcStep tds drained.mono) default))
                from by rw [← Array.foldl_toList]]
            rw [show (drained.newFunctions.foldl (PhaseA2.fnStep tds drained.mono) _)
                = (drained.newFunctions.toList.foldl (PhaseA2.fnStep tds drained.mono) _)
                from by rw [← Array.foldl_toList]]
            exact hfn_list_fold_pres _ _ (hdt_list_fold_pres _ _ hsrc_ex)
          obtain ⟨d_mono, hmono_get⟩ := hmono_some
          have h_kind := step4Lower_fold_kind_at_key hmono_get hconc'
          cases d_mono with
          | function _ => obtain ⟨cf, hcf⟩ := h_kind; exact ⟨_, hcf⟩
          | dataType _ => obtain ⟨cdt', hcdt'⟩ := h_kind; exact ⟨_, hcdt'⟩
          | constructor _ _ => obtain ⟨cdt', cc, hcc⟩ := h_kind; exact ⟨_, hcc⟩
        have hFnNotKey : ∀ f ∈ drained.newFunctions, f.name ≠ g := by
          intro f hf heq
          obtain ⟨g_f, args_f, f_orig, hf_name, hf_get, _⟩ := hSNN.1 f hf
          have heq' : concretizeName g_f args_f = concretizeName g #[] := by
            rw [← hf_name, heq, concretizeName_empty_args]
          have hKey_in_cd : ∃ d, cd.getByKey (concretizeName g_f args_f) = some d := by
            rw [heq', concretizeName_empty_args]; exact hg_in_cd
          obtain ⟨hg_eq, _⟩ :=
            hUnique _hconc g_f g args_f #[] heq' hKey_in_cd
          rw [hg_eq] at hf_get
          rw [hdt_orig_get] at hf_get; cases hf_get
        have hDtCtorNotKey : ∀ dt' ∈ drained.newDataTypes, ∀ c ∈ dt'.constructors,
            dt'.name.pushNamespace c.nameHead ≠ g := by
          intro dt' hdt'_mem c hc heq
          let collisionArg : Typ := .ref ⟨.mkSimple c.nameHead⟩
          have hLHS_eq : concretizeName dt'.name #[collisionArg] =
              dt'.name.pushNamespace c.nameHead :=
            RefClosedBody.concretizeName_singleton_ref_simple dt'.name c.nameHead
          have heq_concName :
              concretizeName dt'.name #[collisionArg] = concretizeName g #[] := by
            rw [hLHS_eq, heq, concretizeName_empty_args]
          have hKey_in_cd' :
              ∃ d, cd.getByKey (concretizeName dt'.name #[collisionArg]) = some d := by
            rw [hLHS_eq, heq]; exact hg_in_cd
          obtain ⟨_, hargs_witness⟩ :=
            hUnique _hconc dt'.name g #[collisionArg] #[] heq_concName hKey_in_cd'
          have h1 : (#[collisionArg] : Array Typ).size = 1 := rfl
          have h0 : (#[collisionArg] : Array Typ).size = 0 := by rw [hargs_witness]; rfl
          omega
        obtain ⟨md_dt', hmono_get⟩ :=
          PhaseA2.concretizeBuild_preserves_dataType_kind_fwd tds drained.mono
            drained.newFunctions drained.newDataTypes hdt_orig_get hdt_params
            hDtCtorNotKey hFnNotKey
        exact step4Lower_fold_dataType_bridge_inline hmono_get hconc'
      have h_cdAt_newDt : ∀ g,
          (∃ newDt ∈ drained.newDataTypes, newDt.name = g) →
          ∃ cdt, cd.getByKey g = some (.dataType cdt) := by
        intro g ⟨newDt, hnewDt_mem, hnewDt_name⟩
        rw [← hnewDt_name]
        obtain ⟨g_orig, args, dt_orig, hname_eq, hdt_orig_get, _hsz, _hctors⟩ :=
          hSNN.2 newDt hnewDt_mem
        have hg_in_cd : ∃ d, cd.getByKey newDt.name = some d :=
          RefClosedBody.cd_has_some_at_newDt_name hconc' hnewDt_mem
        have hFnNotKey : ∀ f ∈ drained.newFunctions, f.name ≠ newDt.name := by
          intro f hf heq
          obtain ⟨g_f, args_f, f_orig, hf_name, hf_get, _⟩ := hSNN.1 f hf
          have heq' : concretizeName g_f args_f = concretizeName g_orig args := by
            rw [← hf_name, heq, hname_eq]
          have hKey_in_cd : ∃ d, cd.getByKey (concretizeName g_f args_f) = some d := by
            rw [heq', ← hname_eq]; exact hg_in_cd
          obtain ⟨hg_eq, _⟩ :=
            hUnique _hconc g_f g_orig args_f args heq' hKey_in_cd
          rw [hg_eq] at hf_get
          rw [hdt_orig_get] at hf_get; cases hf_get
        have hDtCtorNotKey : ∀ dt' ∈ drained.newDataTypes, ∀ c ∈ dt'.constructors,
            dt'.name.pushNamespace c.nameHead ≠ newDt.name := by
          intro dt' hdt'_mem c hc heq
          let collisionArg : Typ := .ref ⟨.mkSimple c.nameHead⟩
          have hLHS_eq : concretizeName dt'.name #[collisionArg] =
              dt'.name.pushNamespace c.nameHead :=
            RefClosedBody.concretizeName_singleton_ref_simple dt'.name c.nameHead
          have heq_concName :
              concretizeName dt'.name #[collisionArg] = concretizeName g_orig args := by
            rw [hLHS_eq, heq, hname_eq]
          have hKey_in_cd' :
              ∃ d, cd.getByKey (concretizeName dt'.name #[collisionArg]) = some d := by
            rw [hLHS_eq, heq]; exact hg_in_cd
          obtain ⟨hname_dt'_eq, hargs_witness⟩ :=
            hUnique _hconc dt'.name g_orig #[collisionArg] args heq_concName hKey_in_cd'
          have hsz_args : args.size = 1 := by rw [← hargs_witness]; rfl
          obtain ⟨g'_orig, args'_dt, dt'_orig, hdt'_name, hdt'_get, hdt'_sz, _⟩ :=
            hSNN.2 dt' hdt'_mem
          have heq2 : concretizeName g'_orig args'_dt = concretizeName g_orig #[] := by
            rw [← hdt'_name, hname_dt'_eq, concretizeName_empty_args]
          have hKey2 : ∃ d, cd.getByKey (concretizeName g'_orig args'_dt) = some d := by
            rw [← hdt'_name]
            exact RefClosedBody.cd_has_some_at_newDt_name hconc' hdt'_mem
          obtain ⟨_hg'_eq, hargs'_eq⟩ :=
            hUnique _hconc g'_orig g_orig args'_dt #[] heq2 hKey2
          have hargs'_size : args'_dt.size = 0 := by rw [hargs'_eq]; rfl
          rw [hargs'_size] at hdt'_sz
          rw [_hg'_eq, hdt_orig_get] at hdt'_get
          have hdt_orig_eq : dt'_orig = dt_orig := by
            have h1 : (Typed.Declaration.dataType dt_orig) =
                .dataType dt'_orig := Option.some.inj hdt'_get
            injection h1.symm
          rw [hdt_orig_eq] at hdt'_sz
          rw [hsz_args] at _hsz
          omega
        obtain ⟨md_dt', hmono_get⟩ :=
          PhaseA2.concretizeBuild_at_newDt_name tds drained.mono drained.newFunctions
            drained.newDataTypes hnewDt_mem hDtCtorNotKey hFnNotKey
        exact step4Lower_fold_dataType_bridge_inline hmono_get hconc'
      have h_cdMono_dt : ∀ (g : Global) (args : Array Typ) (concName : Global),
          (∃ dt, tds.getByKey g = some (.dataType dt)) →
          (∅ : Std.HashMap (Global × Array Typ) Global)[(g, args)]? = some concName →
          ∃ cdt, cd.getByKey concName = some (.dataType cdt) := by
        intro g args concName _ hsome
        simp at hsome
      -- Per-element wiring: each constructor's argTypes elt comes from typToConcrete ∅
      -- on the corresponding md_dt-ctor's argTypes elt.
      intro c hc t ht
      -- Find i with dt.constructors[i] = c, then md_dt.constructors[i] = md_c with
      -- md_c.argTypes mapped via typToConcrete ∅ giving c.argTypes.
      obtain ⟨i, hi_lt_dt, hi_eq⟩ := List.getElem_of_mem hc
      have hi_lt_md : i < md_dt.constructors.length := by rw [hLen] at hi_lt_dt; exact hi_lt_dt
      let md_c := md_dt.constructors[i]'hi_lt_md
      have hmd_c_mem : md_c ∈ md_dt.constructors := List.getElem_mem hi_lt_md
      -- From the mapM witness in step4Lower_dataType_explicit: md_dt.constructors.mapM (... typToConcrete ∅ ...) = .ok dt.constructors.
      -- Per-position: md_c.argTypes.mapM (typToConcrete ∅) = .ok c.argTypes.
      -- Use List.mem_mapM_ok_forall on the per-ctor mapM witness.
      have hctors_perpos :
          ∃ argTypes, md_c.argTypes.mapM
            (typToConcrete (∅ : Std.HashMap (Global × Array Typ) Global)) = .ok argTypes ∧
            ({ nameHead := md_c.nameHead, argTypes } : Concrete.Constructor) =
              dt.constructors[i]'hi_lt_dt := by
        obtain ⟨_, hind⟩ := List.mapM_ok_at_index_lemma _ _ hctors_witness
        obtain ⟨_, hperpos⟩ := hind i hi_lt_md
        -- hperpos : (do { let argTypes ← md_c.argTypes.mapM ...; pure ... }) = .ok dt.constructors[i].
        simp only [bind, Except.bind, pure, Except.pure] at hperpos
        split at hperpos
        · cases hperpos
        rename_i argTypes hatm
        simp only [Except.ok.injEq] at hperpos
        refine ⟨argTypes, hatm, ?_⟩
        rw [hperpos]
      obtain ⟨argTypes_md, hmd_argTypes, hctor_eq⟩ := hctors_perpos
      -- From hctor_eq: c.argTypes = argTypes_md and c.nameHead = md_c.nameHead.
      rw [← hi_eq] at ht
      have hat_eq : (dt.constructors[i]'hi_lt_dt).argTypes = argTypes_md := by
        have h1 := hctor_eq
        -- ({ nameHead := ..., argTypes := argTypes_md } : Concrete.Constructor) = dt.constructors[i].
        have h2 : (({ nameHead := md_c.nameHead, argTypes := argTypes_md } : Concrete.Constructor)).argTypes
            = (dt.constructors[i]'hi_lt_dt).argTypes := by rw [h1]
        exact h2.symm
      rw [hat_eq] at ht
      have hcd_at_name : ∃ d, cd.getByKey name = some d := ⟨_, hcd_get_full⟩
      have h_appCov := dataType_arm_no_app_md_dt _hwf _hdecls _hts hdrain hSSM hARC hPE
        hmd_get hMonoShape hNDFS hUnique hSNN _hconc hcd_at_name
      -- Now apply List.mem_mapM_ok_forall with enriched predicate.
      refine List.mem_mapM_ok_forall
        (P := fun t' =>
          RefClosedBody.Typed.Typ.AppRefToDtOrNewDt tds drained.newDataTypes t' ∧
          (∀ g args (mono : MonoMap),
            RefClosedBody.Typ.containsApp g args t' →
            ∃ concName, mono[(g, args)]? = some concName))
        (Q := fun tc => Concrete.Typ.RefClosed cd tc)
        ?_ md_c.argTypes argTypes_md
        (fun t' ht' => ⟨h_md_AR md_c hmd_c_mem t' ht', h_appCov md_c hmd_c_mem t' ht'⟩)
        hmd_argTypes t ht
      intro t' ⟨ht'_AR, ht'_appCov⟩ fx hfx
      exact RefClosedBody.typToConcrete_RefClosed_via_AppRefToDtOrNewDt
        (mono := ∅) h_cdAt_tds h_cdAt_newDt h_cdMono_dt ht'_AR
        (ht'_appCov · · ∅) hfx
    exact h_dt
  | .constructor cd_dt c, hget =>
    -- Sub-claim A.1-ctor: each c.argTypes element is RefClosed cd.
    have h_c : ∀ t ∈ c.argTypes, Concrete.Typ.RefClosed cd t := by
      -- Extract drained from _hconc; monoDecls = concretizeBuild …
      have hconc' := _hconc
      unfold Typed.Decls.concretize at hconc'
      simp only [bind, Except.bind] at hconc'
      split at hconc'
      · cases hconc'
      rename_i drained hdrain
      -- StrongNewNameShape + MonoShapeOk preserved through drain.
      have hSNN : drained.StrongNewNameShape tds :=
        concretize_drain_preserves_StrongNewNameShape _ _
          (DrainState.StrongNewNameShape.init tds (concretizeSeed tds)) hdrain
      have hMonoShape : drained.MonoShapeOk tds :=
        concretize_drain_shape_equation _ _
          (DrainState.MonoShapeOk.init tds (concretizeSeed tds)) hdrain
      have hNDFS : drained.NewDtFullShape tds :=
        concretize_drain_preserves_NewDtFullShape _ _
          (DrainState.NewDtFullShape.init tds (concretizeSeed tds)) hdrain
      have hSSM : drained.SeenSubsetMono :=
        concretize_drain_preserves_SeenSubsetMono _ _
          (DrainState.SeenSubsetMono.init _) hdrain
      have hARC : drained.AppsReachedCond tds :=
        concretize_drain_preserves_AppsReachedCond _ _
          (DrainState.AppsReachedCond.init tds) hdrain
      have hPE_b : drained.pending.isEmpty :=
        concretize_drain_succeeds_pending_empty _ _ hdrain
      have hPE : ∀ q, q ∈ drained.pending → False := by
        intro q hq
        have hne : drained.pending.isEmpty = false := by
          rw [Std.HashSet.isEmpty_eq_false_iff_exists_contains_eq_true]
          exact ⟨q, Std.HashSet.contains_iff_mem.mpr hq⟩
        rw [hne] at hPE_b; cases hPE_b
      -- Backward: monoDecls has .constructor at name.
      obtain ⟨md_dt, md_c, hmd_get⟩ :=
        step4Lower_backward_ctor_kind_at_key hget hconc'
      -- step4Lower forward: cd_c.argTypes = mapM (typToConcrete ∅) md_c.argTypes.
      obtain ⟨cd_dt', cd_c', hcd_get_full, _hname_eq, _hlen, _hch_eq, _hperpos,
              _hpos_eq, _hctors, hargTypes⟩ :=
        step4Lower_constructor_explicit hmd_get hconc'
      -- Identify cd_c' = c via hget vs hcd_get_full.
      have hsame : (Concrete.Declaration.constructor cd_dt' cd_c') =
          .constructor cd_dt c := by
        rw [hcd_get_full] at hget; exact (Option.some.injEq _ _).mp hget
      have heq_c : cd_c' = c := by injection hsame
      rw [heq_c] at hargTypes
      have hUnique : Typed.Decls.ConcretizeUniqueNames tds :=
        _hwf.noNameCollisions _ _hts
      -- h_md_AR: for every t' ∈ md_c.argTypes, AppRefToDtOrNewDt tds drained.newDataTypes t'.
      -- Origin split on md_c via concretizeBuild_ctor_origin:
      -- (A) source case: tds .ctor at name with src_dt.params=[]; md_c.argTypes =
      --     src_c.argTypes.map (rewriteTyp ∅ drained.mono) via concretizeBuild_at_typed_ctor_explicit
      --     (disjointness via collision-witness). source argTypes wellFormed via
      --     mkDecls_ctor_companion + wellFormedDecls_reflect_dataType. SrcTypRefsAreDtKeys
      --     via SrcTypRefsAreDtKeys_of_wellFormedType. AppRefToDt via #3. AppRefToDtOrNewDt
      --     via #6.
      -- (B) newDt case: dt' ∈ drained.newDataTypes, ∃ c ∈ dt'.constructors with
      --     name = dt'.name.pushNamespace c.nameHead. dtStep inserts .constructor with
      --     md_c.argTypes = c.argTypes (where c is from dt'.constructors, possibly
      --     rewritten by drain). Need drain-emit-AppRefToDt-safe invariant.
      have h_md_AR : ∀ t' ∈ md_c.argTypes,
          RefClosedBody.Typed.Typ.AppRefToDtOrNewDt tds drained.newDataTypes t' := by
        rcases PhaseA2.concretizeBuild_ctor_origin tds drained.mono drained.newFunctions
            drained.newDataTypes hmd_get with
          ⟨src_dt, src_c, hsrc_get, hsrc_params⟩ | ⟨dt_new, hdt_new_mem, c_new, hc_new_mem, hpush_eq⟩
        · -- (A) source case.
          -- Disjointness via collision-witness + hUnique + cd witness at name.
          have hcd_at_name : ∃ d, cd.getByKey name = some d := ⟨_, hcd_get_full⟩
          have hDtNotKey : ∀ dt' ∈ drained.newDataTypes, dt'.name ≠ name := by
            intro dt' hmem heq
            obtain ⟨g_orig, args, dt_orig, hname_eq', hdt_orig_get, _, _⟩ :=
              hSNN.2 dt' hmem
            have heq' : concretizeName g_orig args = concretizeName name #[] := by
              rw [← hname_eq', heq, concretizeName_empty_args]
            have hKey : ∃ d, cd.getByKey (concretizeName g_orig args) = some d := by
              rw [heq', concretizeName_empty_args]; exact hcd_at_name
            obtain ⟨hg_eq, _⟩ := hUnique _hconc g_orig name args #[] heq' hKey
            -- tds has .dataType at g_orig and .ctor at name = g_orig: kind conflict.
            rw [hg_eq] at hdt_orig_get
            rw [hsrc_get] at hdt_orig_get; cases hdt_orig_get
          have hFnNotKey : ∀ f ∈ drained.newFunctions, f.name ≠ name := by
            intro f hmem heq
            obtain ⟨g_orig, args, f_orig, hname_eq', hf_get, _⟩ := hSNN.1 f hmem
            have heq' : concretizeName g_orig args = concretizeName name #[] := by
              rw [← hname_eq', heq, concretizeName_empty_args]
            have hKey : ∃ d, cd.getByKey (concretizeName g_orig args) = some d := by
              rw [heq', concretizeName_empty_args]; exact hcd_at_name
            obtain ⟨hg_eq, _⟩ := hUnique _hconc g_orig name args #[] heq' hKey
            rw [hg_eq] at hf_get
            rw [hsrc_get] at hf_get; cases hf_get
          have hCtorNotKey : ∀ dt' ∈ drained.newDataTypes, ∀ c ∈ dt'.constructors,
              dt'.name.pushNamespace c.nameHead ≠ name := by
            intro dt' hmem c hc heq
            let collisionArg : Typ := .ref ⟨.mkSimple c.nameHead⟩
            have hLHS_eq : concretizeName dt'.name #[collisionArg] =
                dt'.name.pushNamespace c.nameHead :=
              RefClosedBody.concretizeName_singleton_ref_simple dt'.name c.nameHead
            have heq_concName :
                concretizeName dt'.name #[collisionArg] = concretizeName name #[] := by
              rw [hLHS_eq, heq, concretizeName_empty_args]
            have hKey : ∃ d, cd.getByKey (concretizeName dt'.name #[collisionArg]) = some d := by
              rw [hLHS_eq, heq]; exact hcd_at_name
            obtain ⟨_, hargs_eq⟩ :=
              hUnique _hconc dt'.name name #[collisionArg] #[] heq_concName hKey
            have h1 : (#[collisionArg] : Array Typ).size = 1 := rfl
            have h0 : (#[collisionArg] : Array Typ).size = 0 := by rw [hargs_eq]; rfl
            omega
          -- Apply explicit form: md_c.argTypes = src_c.argTypes.map (rewriteTyp ∅ drained.mono).
          have hexplicit :=
            PhaseA2.concretizeBuild_at_typed_ctor_explicit tds drained.mono
              drained.newFunctions drained.newDataTypes hsrc_get hsrc_params
              hDtNotKey hFnNotKey hCtorNotKey
          -- hexplicit: concretizeBuild ... .getByKey name = some (.constructor monoDt monoC)
          --   where monoC.argTypes = src_c.argTypes.map (rewriteTyp ∅ drained.mono).
          -- Combine with hmd_get to get md_c = monoC.
          rw [hexplicit] at hmd_get
          let rewArgs : List Typ := src_c.argTypes.map (rewriteTyp (fun _ => none) drained.mono)
          have hmd_c_eq : md_c = { src_c with argTypes := rewArgs } := by
            have h1 : Typed.Declaration.constructor _ { src_c with argTypes := rewArgs } =
                .constructor md_dt md_c := Option.some.inj hmd_get
            have h2 : { src_c with argTypes := rewArgs } = md_c := by injection h1
            exact h2.symm
          rw [hmd_c_eq]
          show ∀ t' ∈ ({ src_c with argTypes := rewArgs } : Constructor).argTypes,
              RefClosedBody.Typed.Typ.AppRefToDtOrNewDt tds drained.newDataTypes t'
          -- Per-element: each elem of src_c.argTypes.map (rewriteTyp ∅ drained.mono)
          -- satisfies AppRefToDtOrNewDt.
          intro t' ht'_mem
          -- ht'_mem : t' ∈ (src_c.argTypes.map (rewriteTyp ∅ drained.mono))
          obtain ⟨src_t, hsrc_t_mem, ht'_eq⟩ := List.mem_map.mp ht'_mem
          subst ht'_eq
          -- Now goal: AppRefToDtOrNewDt tds drained.newDataTypes (rewriteTyp ∅ drained.mono src_t).
          -- Build wellFormedness chain.
          have hP := FnMatchP_checkAndSimplify _hdecls _hts
          have hsrc_decl_ctor : decls.getByKey name = some (.constructor src_dt src_c) :=
            (hP name).2.2 src_dt src_c hsrc_get
          obtain ⟨hsrc_dt_at_name, hc_mem⟩ :=
            mkDecls_ctor_companion _hdecls name src_dt src_c hsrc_decl_ctor
          have hwf := checkAndSimplify_implies_wellFormedDecls _hdecls _hts
          have hdt_key_name := mkDecls_dt_key_is_name _hdecls
          have hsrc_dt_pair :
              (src_dt.name, Source.Declaration.dataType src_dt) ∈ decls.pairs.toList :=
            IndexMap.mem_pairs_of_getByKey _ _ _ hsrc_dt_at_name
          obtain ⟨vis, vis', hvis_fresh, hwf_dt⟩ :=
            wellFormedDecls_reflect_dataType_fresh hdt_key_name hwf hsrc_dt_pair
          have hwf_argtypes := wellFormedDecls_reflect_dataType hvis_fresh hwf_dt
          -- src_t ∈ src_c.argTypes (we have it via hsrc_t_mem).
          have hwf_t : wellFormedDecls.wellFormedType decls src_dt.params src_t = .ok () :=
            hwf_argtypes src_c hc_mem src_t hsrc_t_mem
          rw [hsrc_params] at hwf_t
          -- Lift to SrcTypRefsAreDtKeys.
          have hSRD := SrcTypRefsAreDtKeys_of_wellFormedType decls [] src_t hwf_t
          -- Lift to AppRefToDt via #3.
          have h_dt_lift : ∀ g, (∃ dt_src, decls.getByKey g = some (.dataType dt_src)) →
              ∃ dt_td, tds.getByKey g = some (.dataType dt_td) := by
            intro g ⟨dt_src, hget_src⟩
            obtain ⟨dt_td, hget_td⟩ := checkAndSimplify_src_dt_to_td _hdecls _hts hget_src
            exact ⟨dt_td, hget_td⟩
          have h_dt_params_lift : ∀ g,
              (∃ dt_src, decls.getByKey g = some (.dataType dt_src) ∧ dt_src.params = []) →
              ∃ dt_td, tds.getByKey g = some (.dataType dt_td) ∧ dt_td.params = [] := by
            intro g ⟨dt_src, hget_src, hparams⟩
            obtain ⟨dt_td, hget_td⟩ := checkAndSimplify_src_dt_to_td _hdecls _hts hget_src
            -- FnMatchP: typed .dataType at g implies source .dataType at g (same dt).
            have hsrc' : decls.getByKey g = some (.dataType dt_td) := (hP g).2.1 dt_td hget_td
            have h1 : Source.Declaration.dataType dt_src = .dataType dt_td := by
              rw [hget_src] at hsrc'
              exact Option.some.inj hsrc'
            have hdt_eq : dt_src = dt_td := by injection h1
            exact ⟨dt_td, hget_td, hdt_eq ▸ hparams⟩
          have hAR := RefClosedBody.AppRefToDt_of_SrcTypRefsAreDtKeys
            h_dt_lift h_dt_params_lift hSRD
          -- Apply #6 (rewriteTyp_preserves_AppRefToDtOrNewDt).
          exact RefClosedBody.rewriteTyp_preserves_AppRefToDtOrNewDt hMonoShape hAR
        · -- (B) newDt case: dt_new ∈ drained.newDataTypes, c_new ∈ dt_new.constructors,
          -- hpush_eq : dt_new.name.pushNamespace c_new.nameHead = name.
          -- Wire `concretizeBuild_at_newDt_ctor_name_explicit` + drain
          -- `CtorArgsAppRefToDt` invariant + `rewriteTyp_preserves_AppRefToDtOrNewDt`.
          have hcd_at_name : ∃ d, cd.getByKey name = some d := ⟨_, hcd_get_full⟩
          -- Disjointness premises for the explicit lemma.
          -- (1) hDtNotKey: ∀ dt' ∈ newDataTypes, dt'.name ≠ name. Use SNN.2 + hUnique
          -- collision-witness.
          have hDtNotKey : ∀ dt' ∈ drained.newDataTypes,
              dt'.name ≠ dt_new.name.pushNamespace c_new.nameHead := by
            intro dt' hmem heq
            -- dt'.name = name (= dt_new.name.pushNamespace c_new.nameHead).
            -- Build name as concretizeName dt_new.name #[collisionArg].
            let collisionArg : Typ := .ref ⟨.mkSimple c_new.nameHead⟩
            have hLHS_eq : concretizeName dt_new.name #[collisionArg] =
                dt_new.name.pushNamespace c_new.nameHead :=
              RefClosedBody.concretizeName_singleton_ref_simple dt_new.name c_new.nameHead
            -- dt'.name = concretizeName dt_new.name #[collisionArg].
            have hdt'_eq : dt'.name = concretizeName dt_new.name #[collisionArg] := by
              rw [hLHS_eq]; exact heq
            -- Derive name shape via SNN.2 on dt' AND dt_new.
            obtain ⟨g_orig', args', dt_orig', hname_eq', hdt_orig_get', hsz', _⟩ :=
              hSNN.2 dt' hmem
            obtain ⟨g_new_orig, args_new, dt_new_orig, hname_eq_new, hdt_new_get,
                    hsz_new, _⟩ := hSNN.2 dt_new hdt_new_mem
            -- dt_new.name = concretizeName g_new_orig args_new.
            -- collisionArg-name eq: concretizeName g_orig' args' = concretizeName dt_new.name #[collisionArg].
            have heq1 : concretizeName g_orig' args' =
                concretizeName dt_new.name #[collisionArg] := by
              rw [← hname_eq', hdt'_eq]
            -- Derive name witness in cd at the LHS form (g_orig', args').
            have hKey1 : ∃ d,
                cd.getByKey (concretizeName g_orig' args') = some d := by
              rw [heq1, hLHS_eq]; rw [← hpush_eq] at hcd_at_name; exact hcd_at_name
            -- hUnique forces g_orig' = dt_new.name and args' = #[collisionArg].
            obtain ⟨hgo_eq, hargs_eq⟩ :=
              hUnique _hconc g_orig' dt_new.name args' #[collisionArg] heq1 hKey1
            -- args'.size = #[collisionArg].size = 1.
            have hsz_args' : args'.size = 1 := by rw [hargs_eq]; rfl
            -- Now also: g_orig' = dt_new.name. But dt_new.name = concretizeName g_new_orig args_new.
            -- So tds.getByKey g_orig' = ... = tds.getByKey (concretizeName g_new_orig args_new).
            -- Combined: g_orig' is a tds dt-key (via hdt_orig_get'). dt_new.name need not be a tds key.
            -- Closure: hgo_eq : g_orig' = dt_new.name. So dt_new.name is a tds dt-key for dt_orig'.
            -- But SNN.2 on dt_new says dt_new.name = concretizeName g_new_orig args_new.
            -- So we have concretizeName g_new_orig args_new = dt_new.name.
            -- And tds.getByKey dt_new.name = some (.dataType dt_orig') (via hgo_eq + hdt_orig_get').
            -- And tds.getByKey g_new_orig = some (.dataType dt_new_orig).
            -- Apply hUnique on (g_new_orig, args_new) vs (dt_new.name, #[]):
            -- concretizeName g_new_orig args_new = concretizeName dt_new.name #[] (via concretizeName_empty_args)?
            -- concretizeName dt_new.name #[] = dt_new.name. So we need:
            --   concretizeName g_new_orig args_new = dt_new.name = concretizeName dt_new.name #[].
            have heq2 : concretizeName g_new_orig args_new =
                concretizeName dt_new.name #[] := by
              rw [concretizeName_empty_args, ← hname_eq_new]
            have hKey2 : ∃ d, cd.getByKey (concretizeName g_new_orig args_new) = some d := by
              rw [← hname_eq_new]
              exact RefClosedBody.cd_has_some_at_newDt_name hconc' hdt_new_mem
            obtain ⟨hg_new_eq, hargs_new_eq⟩ :=
              hUnique _hconc g_new_orig dt_new.name args_new #[] heq2 hKey2
            -- args_new.size = 0 = dt_new_orig.params.length.
            have hsz_an : args_new.size = 0 := by rw [hargs_new_eq]; rfl
            -- Cross: g_orig' = dt_new.name = g_new_orig. So tds at g_orig' = tds at g_new_orig.
            have hg_cross : g_orig' = g_new_orig := by rw [hgo_eq, hg_new_eq]
            rw [hg_cross] at hdt_orig_get'
            rw [hdt_new_get] at hdt_orig_get'
            -- Same dt: dt_orig' = dt_new_orig.
            have hdt_eq : dt_orig' = dt_new_orig := by
              have h1 : Typed.Declaration.dataType dt_new_orig =
                  .dataType dt_orig' := Option.some.inj hdt_orig_get'
              injection h1.symm
            rw [hdt_eq] at hsz'
            -- hsz_new : args_new.size = dt_new_orig.params.length, hsz_an : args_new.size = 0
            -- ⟹ dt_new_orig.params.length = 0.
            have hp_zero : dt_new_orig.params.length = 0 := by rw [← hsz_new, hsz_an]
            rw [hp_zero] at hsz'
            -- args'.size = 0 contradicts args'.size = 1.
            omega
          -- (2) hFnNotKey: ∀ f ∈ newFunctions, f.name ≠ name. Same pattern.
          have hFnNotKey : ∀ f ∈ drained.newFunctions,
              f.name ≠ dt_new.name.pushNamespace c_new.nameHead := by
            intro f hmem heq
            let collisionArg : Typ := .ref ⟨.mkSimple c_new.nameHead⟩
            have hLHS_eq : concretizeName dt_new.name #[collisionArg] =
                dt_new.name.pushNamespace c_new.nameHead :=
              RefClosedBody.concretizeName_singleton_ref_simple dt_new.name c_new.nameHead
            -- f.name = concretizeName g_orig args.
            obtain ⟨g_f_orig, args_f, f_orig, hf_name, hf_get, _⟩ := hSNN.1 f hmem
            obtain ⟨g_new_orig, args_new, dt_new_orig, hname_eq_new, hdt_new_get, _, _⟩ :=
              hSNN.2 dt_new hdt_new_mem
            have heq1 : concretizeName g_f_orig args_f =
                concretizeName dt_new.name #[collisionArg] := by
              rw [← hf_name, heq, ← hLHS_eq]
            have hKey1 : ∃ d,
                cd.getByKey (concretizeName g_f_orig args_f) = some d := by
              rw [heq1, hLHS_eq]; rw [← hpush_eq] at hcd_at_name; exact hcd_at_name
            obtain ⟨hgf_eq, hargs_eq⟩ :=
              hUnique _hconc g_f_orig dt_new.name args_f #[collisionArg] heq1 hKey1
            -- g_f_orig = dt_new.name, so tds has .function at dt_new.name.
            -- But SNN.2 on dt_new: tds has .dataType at dt_new.name (after similar chain).
            -- Use the hg_cross pattern.
            have heq2 : concretizeName g_new_orig args_new =
                concretizeName dt_new.name #[] := by
              rw [concretizeName_empty_args, ← hname_eq_new]
            have hKey2 : ∃ d, cd.getByKey (concretizeName g_new_orig args_new) = some d := by
              rw [← hname_eq_new]
              exact RefClosedBody.cd_has_some_at_newDt_name hconc' hdt_new_mem
            obtain ⟨hg_new_eq, _⟩ :=
              hUnique _hconc g_new_orig dt_new.name args_new #[] heq2 hKey2
            have hg_cross : g_f_orig = g_new_orig := by rw [hgf_eq, hg_new_eq]
            rw [hg_cross] at hf_get
            rw [hdt_new_get] at hf_get
            cases hf_get
          -- Apply explicit lemma. The new signature uses witness over
          -- newDataTypes.toList (some dt' there carries the c' originating
          -- md_c.argTypes), so no hOtherCtorNotKey premise needed.
          obtain ⟨md_at_name, hmd_at_get, hCAR⟩ :=
            PhaseA2.concretizeBuild_at_newDt_ctor_name_explicit tds drained.mono
              drained.newFunctions drained.newDataTypes hdt_new_mem hc_new_mem
              hDtNotKey hFnNotKey
          -- Combine with hmd_get. name = dt_new.name.pushNamespace c_new.nameHead.
          rw [← hpush_eq] at hmd_get
          rw [hmd_at_get] at hmd_get
          have hmd_eq : md_at_name = .constructor md_dt md_c := Option.some.inj hmd_get
          rw [hmd_eq] at hCAR
          -- hCAR : CtorArgsRewrittenFrom newDataTypes.toList drained.mono (.constructor md_dt md_c).
          have hCAR' : ∃ md_dt' md_c',
              (Typed.Declaration.constructor md_dt md_c) =
                .constructor md_dt' md_c' ∧
              ∃ dt' ∈ drained.newDataTypes.toList, ∃ c' ∈ dt'.constructors,
                md_c'.argTypes = c'.argTypes.map (rewriteTyp (fun _ => none) drained.mono) :=
            hCAR
          obtain ⟨md_dt', md_c', hcons_eq, dt', hdt'_mem, c', hc'_mem, hargs_map⟩ := hCAR'
          have hmdc_eq : md_c = md_c' := by
            have h1 : Typed.Declaration.constructor md_dt md_c =
                .constructor md_dt' md_c' := hcons_eq
            injection h1
          rw [← hmdc_eq] at hargs_map
          intro t' ht'_mem
          rw [hargs_map] at ht'_mem
          obtain ⟨src_t, hsrc_t_mem, ht'_eq⟩ := List.mem_map.mp ht'_mem
          subst ht'_eq
          -- Goal: AppRefToDtOrNewDt tds drained.newDataTypes (rewriteTyp ∅ drained.mono src_t).
          -- src_t ∈ c'.argTypes; c' ∈ dt'.constructors; dt' ∈ drained.newDataTypes.
          have hCAR_invariant : drained.CtorArgsAppRefToDt tds :=
            concretize_produces_CtorArgsAppRefToDt _hwf _hdecls _hts hdrain
          have hdt'_mem_arr : dt' ∈ drained.newDataTypes :=
            Array.mem_toList_iff.mp hdt'_mem
          have hAR : Typed.Typ.AppRefToDt tds [] src_t :=
            hCAR_invariant dt' hdt'_mem_arr c' hc'_mem src_t hsrc_t_mem
          exact RefClosedBody.rewriteTyp_preserves_AppRefToDtOrNewDt hMonoShape hAR
      -- h_cdAt_tds: ∀ g, tds dt-key with params=[] ⟹ cd dt-key. Mirrors
      -- h_cdAt_newDt: (1) hg_in_cd via fromSource_inserts_dataType_at_key + foldl
      -- preservation + step4Lower; (2) hFnNotKey via SNN+hUnique+kind-conflict;
      -- (3) hDtCtorNotKey BLOCKED on outer-pushNamespace structure (mirrors
      -- C.1's BLOCKED-D2c); (4) concretizeBuild_preserves_dataType_kind_fwd
      -- + step4Lower bridge.
      have h_cdAt_tds : ∀ g,
          (∃ dt, tds.getByKey g = some (.dataType dt) ∧ dt.params = []) →
          ∃ cdt, cd.getByKey g = some (.dataType cdt) := by
        intro g ⟨dt_orig, hdt_orig_get, hdt_params⟩
        -- (1) cd has SOME entry at g via fromSource → fold preservation → step4Lower.
        have hg_in_cd : ∃ d, cd.getByKey g = some d := by
          have hinsert_pres : ∀ (acc : Typed.Decls) (k : Global) (v : Typed.Declaration),
              (∃ d, acc.getByKey g = some d) →
              ∃ d, (acc.insert k v).getByKey g = some d := by
            intro acc k v ⟨d, hget⟩
            by_cases hbeq : (k == g) = true
            · have hkeq : k = g := LawfulBEq.eq_of_beq hbeq
              rw [hkeq]; exact ⟨v, IndexMap.getByKey_insert_self _ _ _⟩
            · have hne : (k == g) = false := Bool.not_eq_true _ |>.mp hbeq
              exact ⟨d, by rw [IndexMap.getByKey_insert_of_beq_false _ _ hne]; exact hget⟩
          have hfn_pres : ∀ (acc : Typed.Decls) (f : Typed.Function),
              (∃ d, acc.getByKey g = some d) →
              ∃ d, (PhaseA2.fnStep tds drained.mono acc f).getByKey g = some d := by
            intro acc f hacc
            unfold PhaseA2.fnStep
            exact hinsert_pres acc _ _ hacc
          have hdt_inner_pres : ∀ (acc : Typed.Decls) (newDt' : DataType)
              (dt_outer : DataType) (cs : List Constructor),
              (∃ d, acc.getByKey g = some d) →
              ∃ d, (cs.foldl
                (fun acc'' c =>
                  acc''.insert (dt_outer.name.pushNamespace c.nameHead)
                    (.constructor newDt' c)) acc).getByKey g = some d := by
            intro acc newDt' dt_outer cs hacc
            induction cs generalizing acc with
            | nil => exact hacc
            | cons c rest ih =>
              simp only [List.foldl_cons]
              apply ih
              exact hinsert_pres acc _ _ hacc
          have hdt_pres : ∀ (acc : Typed.Decls) (dt' : DataType),
              (∃ d, acc.getByKey g = some d) →
              ∃ d, (PhaseA2.dtStep drained.mono acc dt').getByKey g = some d := by
            intro acc dt' hacc
            simp only [PhaseA2.dtStep]
            apply hdt_inner_pres
            exact hinsert_pres acc _ _ hacc
          have hdt_list_fold_pres : ∀ (l : List DataType) (init : Typed.Decls),
              (∃ d, init.getByKey g = some d) →
              ∃ d, (l.foldl (PhaseA2.dtStep drained.mono) init).getByKey g = some d := by
            intro l
            induction l with
            | nil => intro init h; exact h
            | cons hd rest ih =>
              intro init h
              simp only [List.foldl_cons]
              exact ih _ (hdt_pres _ hd h)
          have hfn_list_fold_pres : ∀ (l : List Typed.Function) (init : Typed.Decls),
              (∃ d, init.getByKey g = some d) →
              ∃ d, (l.foldl (PhaseA2.fnStep tds drained.mono) init).getByKey g = some d := by
            intro l
            induction l with
            | nil => intro init h; exact h
            | cons hd rest ih =>
              intro init h
              simp only [List.foldl_cons]
              exact ih _ (hfn_pres _ hd h)
          have hmono_some : ∃ d, (concretizeBuild tds drained.mono drained.newFunctions
              drained.newDataTypes).getByKey g = some d := by
            rw [PhaseA2.concretizeBuild_eq]
            obtain ⟨md_dt, hsrc⟩ :=
              PhaseA2.fromSource_inserts_dataType_at_key tds drained.mono hdt_orig_get hdt_params
            have hsrc_ex : ∃ d, (tds.pairs.foldl (PhaseA2.srcStep tds drained.mono)
                default).getByKey g = some d := ⟨_, hsrc⟩
            rw [show (drained.newDataTypes.foldl (PhaseA2.dtStep drained.mono)
                  (tds.pairs.foldl (PhaseA2.srcStep tds drained.mono) default))
                = (drained.newDataTypes.toList.foldl (PhaseA2.dtStep drained.mono)
                    (tds.pairs.foldl (PhaseA2.srcStep tds drained.mono) default))
                from by rw [← Array.foldl_toList]]
            rw [show (drained.newFunctions.foldl (PhaseA2.fnStep tds drained.mono) _)
                = (drained.newFunctions.toList.foldl (PhaseA2.fnStep tds drained.mono) _)
                from by rw [← Array.foldl_toList]]
            exact hfn_list_fold_pres _ _ (hdt_list_fold_pres _ _ hsrc_ex)
          obtain ⟨d_mono, hmono_get⟩ := hmono_some
          have h_kind := step4Lower_fold_kind_at_key hmono_get hconc'
          cases d_mono with
          | function _ => obtain ⟨cf, hcf⟩ := h_kind; exact ⟨_, hcf⟩
          | dataType _ => obtain ⟨cdt', hcdt'⟩ := h_kind; exact ⟨_, hcdt'⟩
          | constructor _ _ => obtain ⟨cdt', cc, hcc⟩ := h_kind; exact ⟨_, hcc⟩
        -- (2) hFnNotKey via SNN+hUnique+kind-conflict.
        have hFnNotKey : ∀ f ∈ drained.newFunctions, f.name ≠ g := by
          intro f hf heq
          obtain ⟨g_f, args_f, f_orig, hf_name, hf_get, _hf_sz⟩ := hSNN.1 f hf
          have heq' : concretizeName g_f args_f = concretizeName g #[] := by
            rw [← hf_name, heq, concretizeName_empty_args]
          have hKey_in_cd : ∃ d, cd.getByKey (concretizeName g_f args_f) = some d := by
            rw [heq', concretizeName_empty_args]; exact hg_in_cd
          obtain ⟨hg_eq, _hargs_eq⟩ :=
            hUnique _hconc g_f g args_f #[] heq' hKey_in_cd
          rw [hg_eq] at hf_get
          rw [hdt_orig_get] at hf_get; cases hf_get
        -- (3) hDtCtorNotKey via collision-witness type-arg + hUnique + args.size mismatch.
        -- Simpler than h_cdAt_newDt's case: g is a tds dt-key, so g = concretizeName g #[]
        -- directly. hUnique forces #[collisionArg] = #[], contradicting size.
        have hDtCtorNotKey : ∀ dt' ∈ drained.newDataTypes, ∀ c ∈ dt'.constructors,
            dt'.name.pushNamespace c.nameHead ≠ g := by
          intro dt' hdt'_mem c hc heq
          let collisionArg : Typ := .ref ⟨.mkSimple c.nameHead⟩
          have hLHS_eq : concretizeName dt'.name #[collisionArg] =
              dt'.name.pushNamespace c.nameHead :=
            RefClosedBody.concretizeName_singleton_ref_simple dt'.name c.nameHead
          have heq_concName :
              concretizeName dt'.name #[collisionArg] = concretizeName g #[] := by
            rw [hLHS_eq, heq, concretizeName_empty_args]
          have hKey_in_cd' :
              ∃ d, cd.getByKey (concretizeName dt'.name #[collisionArg]) = some d := by
            rw [hLHS_eq, heq]; exact hg_in_cd
          obtain ⟨_hname_eq, hargs_witness⟩ :=
            hUnique _hconc dt'.name g #[collisionArg] #[] heq_concName hKey_in_cd'
          have hsz_lhs : (#[collisionArg] : Array Typ).size = 1 := rfl
          have hsz_rhs : (#[collisionArg] : Array Typ).size = 0 := by
            rw [hargs_witness]; rfl
          omega
        -- (4) concretizeBuild_preserves_dataType_kind_fwd + step4Lower bridge.
        obtain ⟨md_dt, hmono_get⟩ :=
          PhaseA2.concretizeBuild_preserves_dataType_kind_fwd tds drained.mono
            drained.newFunctions drained.newDataTypes hdt_orig_get hdt_params
            hDtCtorNotKey hFnNotKey
        exact step4Lower_fold_dataType_bridge_inline hmono_get hconc'
      -- h_cdAt_newDt: ∀ g, newDt-name ⟹ cd dt-key. Closure path:
      -- (1) `hg_in_cd_at_newDt` (~80 LoC inline): every newDt.name is some-keyed
      --     in cd via dtStep insert + foldl preservation + step4Lower.
      -- (2) hFnNotKey via SNN+hUnique+kind-conflict.
      -- (3) hDtCtorNotKey BLOCKED on outer-pushNamespace structure (mirrors
      --     C.1's BLOCKED-D2c).
      -- (4) `concretizeBuild_at_newDt_name` + `step4Lower_fold_dataType_bridge_inline`.
      have h_cdAt_newDt : ∀ g,
          (∃ newDt ∈ drained.newDataTypes, newDt.name = g) →
          ∃ cdt, cd.getByKey g = some (.dataType cdt) := by
        intro g ⟨newDt, hnewDt_mem, hnewDt_name⟩
        rw [← hnewDt_name]
        obtain ⟨g_orig, args, dt_orig, hname_eq, hdt_orig_get, _hsz, _hctors⟩ :=
          hSNN.2 newDt hnewDt_mem
        -- (1) cd has SOME entry at newDt.name. Mirror SizeBound's hg_in_cd
        -- pattern: dtStep on newDt inserts at newDt.name; fold preserves; step4Lower lifts.
        have hg_in_cd : ∃ d, cd.getByKey newDt.name = some d := by
          have hinsert_pres : ∀ (acc : Typed.Decls) (k : Global) (v : Typed.Declaration),
              (∃ d, acc.getByKey newDt.name = some d) →
              ∃ d, (acc.insert k v).getByKey newDt.name = some d := by
            intro acc k v ⟨d, hget⟩
            by_cases hbeq : (k == newDt.name) = true
            · have hkeq : k = newDt.name := LawfulBEq.eq_of_beq hbeq
              rw [hkeq]; exact ⟨v, IndexMap.getByKey_insert_self _ _ _⟩
            · have hne : (k == newDt.name) = false := Bool.not_eq_true _ |>.mp hbeq
              exact ⟨d, by rw [IndexMap.getByKey_insert_of_beq_false _ _ hne]; exact hget⟩
          have hfn_pres : ∀ (acc : Typed.Decls) (f : Typed.Function),
              (∃ d, acc.getByKey newDt.name = some d) →
              ∃ d, (PhaseA2.fnStep tds drained.mono acc f).getByKey newDt.name = some d := by
            intro acc f hacc
            unfold PhaseA2.fnStep
            exact hinsert_pres acc _ _ hacc
          have hdt_inner_pres : ∀ (acc : Typed.Decls) (newDt' : DataType)
              (dt_outer : DataType) (cs : List Constructor),
              (∃ d, acc.getByKey newDt.name = some d) →
              ∃ d, (cs.foldl
                (fun acc'' c =>
                  acc''.insert (dt_outer.name.pushNamespace c.nameHead)
                    (.constructor newDt' c)) acc).getByKey newDt.name = some d := by
            intro acc newDt' dt_outer cs hacc
            induction cs generalizing acc with
            | nil => exact hacc
            | cons c rest ih =>
              simp only [List.foldl_cons]
              apply ih
              exact hinsert_pres acc _ _ hacc
          have hdt_pres : ∀ (acc : Typed.Decls) (dt' : DataType),
              (∃ d, acc.getByKey newDt.name = some d) →
              ∃ d, (PhaseA2.dtStep drained.mono acc dt').getByKey newDt.name = some d := by
            intro acc dt' hacc
            simp only [PhaseA2.dtStep]
            apply hdt_inner_pres
            exact hinsert_pres acc _ _ hacc
          have hdt_fold_pres : ∀ (init : Typed.Decls),
              (∃ d, init.getByKey newDt.name = some d) →
              ∃ d, (drained.newDataTypes.foldl (PhaseA2.dtStep drained.mono) init).getByKey
                newDt.name = some d := by
            intro init hinit
            apply Array.foldl_induction
              (motive := fun (_ : Nat) (acc : Typed.Decls) =>
                ∃ d, acc.getByKey newDt.name = some d) hinit
            intro i acc hacc
            exact hdt_pres acc _ hacc
          have hfn_fold_pres : ∀ (init : Typed.Decls),
              (∃ d, init.getByKey newDt.name = some d) →
              ∃ d, (drained.newFunctions.foldl (PhaseA2.fnStep tds drained.mono) init).getByKey
                newDt.name = some d := by
            intro init hinit
            apply Array.foldl_induction
              (motive := fun (_ : Nat) (acc : Typed.Decls) =>
                ∃ d, acc.getByKey newDt.name = some d) hinit
            intro i acc hacc
            exact hfn_pres acc _ hacc
          -- Find newDt's position in newDataTypes. dtStep at newDt inserts
          -- `.dataType` at newDt.name. Apply foldl preservation pattern.
          have hmono_some : ∃ d, (concretizeBuild tds drained.mono drained.newFunctions
              drained.newDataTypes).getByKey newDt.name = some d := by
            rw [PhaseA2.concretizeBuild_eq]
            -- Split newDataTypes into pre ++ newDt :: post via Array.mem.
            obtain ⟨pre, post, hsplit⟩ :=
              List.append_of_mem (Array.mem_toList_iff.mpr hnewDt_mem)
            rw [show (drained.newDataTypes.foldl (PhaseA2.dtStep drained.mono)
                  (tds.pairs.foldl (PhaseA2.srcStep tds drained.mono) default))
                = (drained.newDataTypes.toList.foldl (PhaseA2.dtStep drained.mono)
                    (tds.pairs.foldl (PhaseA2.srcStep tds drained.mono) default))
                from by rw [← Array.foldl_toList]]
            rw [hsplit, List.foldl_append, List.foldl_cons]
            -- After dtStep on newDt, .dataType is at newDt.name.
            have h_dtstep_some :
                ∃ d, (PhaseA2.dtStep drained.mono
                  (pre.foldl (PhaseA2.dtStep drained.mono)
                    (tds.pairs.foldl (PhaseA2.srcStep tds drained.mono) default))
                  newDt).getByKey newDt.name = some d := by
              obtain ⟨md_dt, hmd⟩ :=
                PhaseA2.dtStep_inserts_dataType_at_self drained.mono _ newDt
              exact ⟨_, hmd⟩
            -- Post fold preserves SOME at newDt.name.
            -- Generic list foldl preservation lemma.
            have hdt_list_fold_pres : ∀ (l : List DataType) (init : Typed.Decls),
                (∃ d, init.getByKey newDt.name = some d) →
                ∃ d, (l.foldl (PhaseA2.dtStep drained.mono) init).getByKey
                  newDt.name = some d := by
              intro l
              induction l with
              | nil => intro init h; exact h
              | cons hd rest ih =>
                intro init h
                simp only [List.foldl_cons]
                exact ih _ (hdt_pres _ hd h)
            have hpost_pres := hdt_list_fold_pres post _ h_dtstep_some
            exact hfn_fold_pres _ hpost_pres
          obtain ⟨d_mono, hmono_get⟩ := hmono_some
          have h_kind := step4Lower_fold_kind_at_key hmono_get hconc'
          cases d_mono with
          | function _ => obtain ⟨cf, hcf⟩ := h_kind; exact ⟨_, hcf⟩
          | dataType _ => obtain ⟨cdt', hcdt'⟩ := h_kind; exact ⟨_, hcdt'⟩
          | constructor _ _ => obtain ⟨cdt', cc, hcc⟩ := h_kind; exact ⟨_, hcc⟩
        -- (2) hFnNotKey via SNN+hUnique+kind-conflict.
        have hFnNotKey : ∀ f ∈ drained.newFunctions, f.name ≠ newDt.name := by
          intro f hf heq
          obtain ⟨g_f, args_f, f_orig, hf_name, hf_get, _hf_sz⟩ := hSNN.1 f hf
          have heq' : concretizeName g_f args_f = concretizeName g_orig args := by
            rw [← hf_name, heq, hname_eq]
          have hKey_in_cd : ∃ d, cd.getByKey (concretizeName g_f args_f) = some d := by
            rw [heq', ← hname_eq]; exact hg_in_cd
          obtain ⟨hg_eq, _hargs_eq⟩ :=
            hUnique _hconc g_f g_orig args_f args heq' hKey_in_cd
          rw [hg_eq] at hf_get
          rw [hdt_orig_get] at hf_get; cases hf_get
        -- (3) hDtCtorNotKey via collision-witness type-arg + hUnique + SNN args.size mismatch.
        -- pushNamespace s = concretizeName g #[.ref ⟨.mkSimple s⟩] (single-limb Typ.ref appendNameLimbs).
        -- hUnique forces dt'.name = g_orig ∧ args = #[ref-arg], so args.size = 1.
        -- SNN.2 dt' chain forces args' = #[] for dt' (giving dt'_orig.params.length = 0).
        -- But dt'_orig = dt_orig (via tds key/kind injectivity), and dt_orig.params.length = 1.
        -- Contradiction.
        have hDtCtorNotKey : ∀ dt' ∈ drained.newDataTypes, ∀ c ∈ dt'.constructors,
            dt'.name.pushNamespace c.nameHead ≠ newDt.name := by
          intro dt' hdt'_mem c hc heq
          let collisionArg : Typ := .ref ⟨.mkSimple c.nameHead⟩
          have hLHS_eq : concretizeName dt'.name #[collisionArg] =
              dt'.name.pushNamespace c.nameHead :=
            RefClosedBody.concretizeName_singleton_ref_simple dt'.name c.nameHead
          have heq_concName :
              concretizeName dt'.name #[collisionArg] = concretizeName g_orig args := by
            rw [hLHS_eq, heq, hname_eq]
          have hKey_in_cd' :
              ∃ d, cd.getByKey (concretizeName dt'.name #[collisionArg]) = some d := by
            rw [hLHS_eq, heq]; exact hg_in_cd
          obtain ⟨hname_dt'_eq, hargs_witness⟩ :=
            hUnique _hconc dt'.name g_orig #[collisionArg] args heq_concName hKey_in_cd'
          have hsz_args : args.size = 1 := by rw [← hargs_witness]; rfl
          obtain ⟨g'_orig, args'_dt, dt'_orig, hdt'_name, hdt'_get, hdt'_sz, _⟩ :=
            hSNN.2 dt' hdt'_mem
          have heq2 : concretizeName g'_orig args'_dt = concretizeName g_orig #[] := by
            rw [← hdt'_name, hname_dt'_eq, concretizeName_empty_args]
          have hKey2 : ∃ d, cd.getByKey (concretizeName g'_orig args'_dt) = some d := by
            rw [← hdt'_name]
            exact RefClosedBody.cd_has_some_at_newDt_name hconc' hdt'_mem
          obtain ⟨_hg'_eq, hargs'_eq⟩ :=
            hUnique _hconc g'_orig g_orig args'_dt #[] heq2 hKey2
          have hargs'_size : args'_dt.size = 0 := by rw [hargs'_eq]; rfl
          rw [hargs'_size] at hdt'_sz
          rw [_hg'_eq, hdt_orig_get] at hdt'_get
          have hdt_orig_eq : dt'_orig = dt_orig := by
            have h1 : (Typed.Declaration.dataType dt_orig) =
                .dataType dt'_orig := Option.some.inj hdt'_get
            injection h1.symm
          rw [hdt_orig_eq] at hdt'_sz
          rw [hsz_args] at _hsz
          omega
        -- (4) concretizeBuild_at_newDt_name + step4Lower bridge.
        obtain ⟨md_dt, hmono_get⟩ :=
          PhaseA2.concretizeBuild_at_newDt_name tds drained.mono drained.newFunctions
            drained.newDataTypes hnewDt_mem hDtCtorNotKey hFnNotKey
        exact step4Lower_fold_dataType_bridge_inline hmono_get hconc'
      -- typToConcrete is invoked with EMPTY mono (per step4Lower). hcdMono_dt
      -- is therefore vacuous: ∅[k]? = none ⟹ the `some _` premise can't fire.
      have h_cdMono_dt : ∀ (g : Global) (args : Array Typ) (concName : Global),
          (∃ dt, tds.getByKey g = some (.dataType dt)) →
          (∅ : Std.HashMap (Global × Array Typ) Global)[(g, args)]? = some concName →
          ∃ cdt, cd.getByKey concName = some (.dataType cdt) := by
        intro g args concName _ hsome
        simp at hsome
      have hcd_at_name : ∃ d, cd.getByKey name = some d := ⟨_, hcd_get_full⟩
      have h_appCov := constructor_arm_no_app_md_c _hwf _hdecls _hts hdrain hSSM hARC hPE
        hmd_get hMonoShape hNDFS hUnique hSNN _hconc hcd_at_name
      -- Per-element wiring: each cd_c.argTypes elt comes from typToConcrete ∅ on
      -- the corresponding md_c.argTypes elt; discharge via the umbrella helper.
      intro t ht
      refine List.mem_mapM_ok_forall
        (P := fun t' =>
          RefClosedBody.Typed.Typ.AppRefToDtOrNewDt tds drained.newDataTypes t' ∧
          (∀ g args (mono : MonoMap),
            RefClosedBody.Typ.containsApp g args t' →
            ∃ concName, mono[(g, args)]? = some concName))
        (Q := fun tc => Concrete.Typ.RefClosed cd tc)
        ?_ md_c.argTypes c.argTypes
        (fun t' ht' => ⟨h_md_AR t' ht', h_appCov t' ht'⟩) hargTypes t ht
      intro t' ⟨ht'_AR, ht'_appCov⟩ fx hfx
      exact RefClosedBody.typToConcrete_RefClosed_via_AppRefToDtOrNewDt
        (mono := ∅) h_cdAt_tds h_cdAt_newDt h_cdMono_dt ht'_AR
        (ht'_appCov · · ∅) hfx
    exact h_c

-- `Typed.Typ.ParamSafe` and `Typed.Decls.NoDirectDatatypeCycles` now live
-- in `Ix.Aiur.Semantics.WellFormed` so the `WellFormed` obligation can reference
-- them.

-- SizeBoundOk + Typ.sizeBound under SpineRefsBelow moved to
-- `ConcretizeSound/SizeBound.lean` 2026-04-29.

/-! ### Source-side lift: `WellFormed t` + `checkAndSimplify` ⟹
`Typed.Decls.AllCtorArgsAppRefToDt tds`.

The two theorems `AllCtorArgsAppRefToDt_of_wellFormed` and
`concretize_produces_CtorArgsAppRefToDt` are defined EARLIER in this file
(just before `concretize_produces_refClosed_entry`) so the umbrella's
`.ctor`-newDt arm can apply them via forward reference.

The polymorphic dt case (`dt.params ≠ []`) is now handled: both
`SrcTypRefsAreDtKeys` (CheckSound.lean) and `Typed.Typ.AppRefToDt` carry a
`params : List String` context, with a dedicated `.refTypeParam` arm for
type-parameter references. The drain layer consumes the per-template
parameterized `AllCtorArgs/AllFnInputs/AllFnOutputAppRefToDt` invariants and
substitutes parameters away via `Typ.instantiate_preserves_AppRefToDt`. -/

end Aiur

end -- public section
