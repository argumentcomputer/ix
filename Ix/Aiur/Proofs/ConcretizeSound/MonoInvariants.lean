module
public import Ix.Aiur.Proofs.ConcretizeSound

/-!
Phase 2 — concretize structural invariants: `MonoHasDecl`, `MonoShapeOk`,
and helpers for `concretize_build_excludes_polymorphic` (reverse direction).
Extracted from `ConcretizeSound.lean` 2026-04-29.
-/

public section

namespace Aiur

open Source

/-! ### Phase 2 — Concretize structural invariants.

Each is a direct structural consequence of `concretizeSeed`/`concretizeDrain`/
`concretizeBuild`'s pure-fold decomposition. Sorried here, no upstream
refactor blockers remain (those were resolved in the pure-fold refactor). -/

/-! ### `concretizeDrain` preserves `MonoHasDecl`

Every specialized `(g, args) ↦ g'` pair in `drained.mono` has a matching entry
in `drained.newFunctions` or `drained.newDataTypes`.

Signature fix (red-team finding): original signature took arbitrary `init`
with no invariant, which was refutable — e.g. `init.mono = {(g, args) ↦ g'}`
with `init.newFunctions = init.newDataTypes = #[]` under `fuel = 0` and
`init.pending = ∅` falsifies the conclusion. The fix adds an invariant
precondition on `init` (trivial for `MonoHasDecl.init`) and strengthens the
conclusion to the same predicate at `drained`.

Proof is by fuel-induction with two helpers below. -/

/-- Helper: a single `concretizeDrainEntry` step preserves `MonoHasDecl`. -/
theorem concretizeDrainEntry_preserves_MonoHasDecl
    {decls : Typed.Decls} {state state' : DrainState}
    (hinv : state.MonoHasDecl) (entry : Global × Array Typ)
    (hstep : concretizeDrainEntry decls state entry = .ok state') :
    state'.MonoHasDecl := by
  unfold concretizeDrainEntry at hstep
  simp only [bind, Except.bind, pure, Except.pure] at hstep
  by_cases hseen : state.seen.contains (entry.1, entry.2)
  · -- seen: state' = state
    simp [hseen] at hstep
    rw [← hstep]
    exact hinv
  · simp [hseen] at hstep
    -- destructure based on getByKey
    split at hstep
    · -- .function case
      rename_i f
      split at hstep
      · -- success: lengths match
        simp only [Except.ok.injEq] at hstep
        rw [← hstep]
        intro g args g' hmono
        -- hmono: (state.mono.insert (entry.1, entry.2) concName)[(g, args)]? = some g'
        rw [Std.HashMap.getElem?_insert] at hmono
        split at hmono
        · -- key match → g' = concretizeName entry.1 entry.2 = new fn name
          rename_i hbeq
          simp only [Option.some.injEq] at hmono
          left
          refine ⟨_, Array.mem_push_self, ?_⟩
          exact hmono
        · -- key no match → falls through to state.mono
          have := hinv g args g' hmono
          rcases this with ⟨f, hfmem, hfname⟩ | ⟨dt, hdtmem, hdtname⟩
          · left
            refine ⟨f, ?_, hfname⟩
            exact Array.mem_push_of_mem _ hfmem
          · right
            exact ⟨dt, hdtmem, hdtname⟩
      · -- throw: lengths differ
        cases hstep
    · -- .dataType case
      rename_i dt
      split at hstep
      · -- success: lengths match
        simp only [Except.ok.injEq] at hstep
        rw [← hstep]
        intro g args g' hmono
        rw [Std.HashMap.getElem?_insert] at hmono
        split at hmono
        · rename_i hbeq
          simp only [Option.some.injEq] at hmono
          right
          refine ⟨_, Array.mem_push_self, ?_⟩
          exact hmono
        · have := hinv g args g' hmono
          rcases this with ⟨f, hfmem, hfname⟩ | ⟨dt', hdtmem, hdtname⟩
          · left; exact ⟨f, hfmem, hfname⟩
          · right
            refine ⟨dt', ?_, hdtname⟩
            exact Array.mem_push_of_mem _ hdtmem
      · -- throw: lengths differ
        cases hstep
    · -- error case from match: .constructor or none
      cases hstep

/-- Helper: folding `concretizeDrainEntry` over a list preserves `MonoHasDecl`. -/
theorem concretizeDrainEntry_list_foldlM_preserves_MonoHasDecl
    {decls : Typed.Decls}
    (L : List (Global × Array Typ))
    (state0 state' : DrainState)
    (hinv0 : state0.MonoHasDecl)
    (hstep : L.foldlM (concretizeDrainEntry decls) state0 = .ok state') :
    state'.MonoHasDecl := by
  induction L generalizing state0 with
  | nil =>
    simp only [List.foldlM, pure, Except.pure, Except.ok.injEq] at hstep
    rw [← hstep]
    exact hinv0
  | cons hd tl ih =>
    simp only [List.foldlM, bind, Except.bind] at hstep
    split at hstep
    · cases hstep
    · rename_i s'' hs''
      have hinv1 : s''.MonoHasDecl :=
        concretizeDrainEntry_preserves_MonoHasDecl hinv0 hd hs''
      exact ih s'' hinv1 hstep

/-- Helper: `concretizeDrainIter` preserves `MonoHasDecl`. -/
theorem concretizeDrainIter_preserves_MonoHasDecl
    {decls : Typed.Decls} {state state' : DrainState}
    (hinv : state.MonoHasDecl)
    (hstep : concretizeDrainIter decls state = .ok state') :
    state'.MonoHasDecl := by
  unfold concretizeDrainIter at hstep
  -- state0 := {state with pending := {}} still has MonoHasDecl (mono, arrays unchanged)
  rw [← Array.foldlM_toList] at hstep
  let state0 : DrainState := { state with pending := ∅ }
  have hinv0 : state0.MonoHasDecl := hinv
  exact concretizeDrainEntry_list_foldlM_preserves_MonoHasDecl
    state.pending.toArray.toList state0 state' hinv0 hstep

/-- `concretizeDrain` preserves `MonoHasDecl`. -/
theorem concretize_drain_mono_has_decl
    {decls : Typed.Decls} (fuel : Nat) (init : DrainState)
    (_hinv : init.MonoHasDecl)
    {drained : DrainState}
    (_hdrain : concretizeDrain decls fuel init = .ok drained) :
    drained.MonoHasDecl := by
  induction fuel generalizing init with
  | zero =>
    unfold concretizeDrain at _hdrain
    by_cases hpen : init.pending.isEmpty
    · simp only [hpen, if_true, pure, Except.pure, Except.ok.injEq] at _hdrain
      rw [← _hdrain]
      exact _hinv
    · simp [hpen] at _hdrain
  | succ n ih =>
    unfold concretizeDrain at _hdrain
    by_cases hpen : init.pending.isEmpty
    · simp only [hpen, if_true, pure, Except.pure, Except.ok.injEq] at _hdrain
      rw [← _hdrain]
      exact _hinv
    · simp only [hpen, if_false, Bool.false_eq_true] at _hdrain
      simp only [bind, Except.bind] at _hdrain
      split at _hdrain
      · cases _hdrain
      · rename_i state' hstate'
        have hinv' : state'.MonoHasDecl :=
          concretizeDrainIter_preserves_MonoHasDecl _hinv hstate'
        exact ih state' hinv' _hdrain

/-! ### `concretizeDrain` preserves `MonoShapeOk`.

For every `(g, args) ↦ g'` in the drained mono where `decls[g] = .dataType dt`,
the drained `newDataTypes` contains a `newDt` with `newDt.name = g'` and
`newDt.constructors = dt.constructors.map` pointwise instantiated by
`mkParamSubst dt.params args`.

Signature fix (red-team finding, mirrors the `MonoHasDecl` case): original
signature took arbitrary `init` with no invariant, refutable by
`init.mono = {(g, args) ↦ g'}` with `init.newDataTypes = #[]` under `fuel = 0`
and empty pending. The fix adds `MonoShapeOk` as both precondition on `init`
(discharged via `MonoShapeOk.init`) and conclusion at `drained`.

Proof is by fuel-induction with three helpers. -/

/-- Helper: a single `concretizeDrainEntry` step preserves `MonoShapeOk`. -/
theorem concretizeDrainEntry_preserves_MonoShapeOk
    {decls : Typed.Decls} {state state' : DrainState}
    (hinv : state.MonoShapeOk decls) (entry : Global × Array Typ)
    (hstep : concretizeDrainEntry decls state entry = .ok state') :
    state'.MonoShapeOk decls := by
  unfold concretizeDrainEntry at hstep
  simp only [bind, Except.bind, pure, Except.pure] at hstep
  by_cases hseen : state.seen.contains (entry.1, entry.2)
  · -- seen: state' = state
    simp [hseen] at hstep
    rw [← hstep]
    exact hinv
  · simp [hseen] at hstep
    -- destructure based on getByKey
    split at hstep
    · -- .function arm: new mono entry points at a FUNCTION; the shape conclusion
      -- asks about a DATATYPE entry, so the fresh-key case contradicts the
      -- template lookup. The fall-through case comes from `hinv` unchanged.
      rename_i f hlook
      split at hstep
      · -- success: lengths match
        simp only [Except.ok.injEq] at hstep
        rw [← hstep]
        intro g args g' hmono dt hdt
        rw [Std.HashMap.getElem?_insert] at hmono
        split at hmono
        · -- key match → entry = (g, args), so `name = g`.
          rename_i hbeq
          have hpair : (entry.1, entry.2) = (g, args) :=
            LawfulBEq.eq_of_beq hbeq
          have hname_g : entry.1 = g := (Prod.mk.injEq ..).mp hpair |>.1
          -- `decls.getByKey entry.1 = some (.function f)` and
          -- `decls.getByKey g = some (.dataType dt)` contradict via `hname_g`.
          rw [hname_g] at hlook
          rw [hlook] at hdt
          cases hdt
        · -- key no match → falls through to state.mono
          have := hinv g args g' hmono hdt
          rcases this with ⟨newDt, hmem, hname, hctors⟩
          -- state'.newDataTypes = state.newDataTypes (unchanged in .function arm)
          exact ⟨newDt, hmem, hname, hctors⟩
      · -- throw: lengths differ
        cases hstep
    · -- .dataType arm: new mono entry points at a DATATYPE
      rename_i templateDt hlook
      split at hstep
      · -- success: lengths match
        simp only [Except.ok.injEq] at hstep
        rw [← hstep]
        intro g args g' hmono dt hdt
        rw [Std.HashMap.getElem?_insert] at hmono
        split at hmono
        · -- key match → entry = (g, args), so `name = g` and `dt = templateDt`
          rename_i hbeq
          have hpair : (entry.1, entry.2) = (g, args) :=
            LawfulBEq.eq_of_beq hbeq
          have hname_g : entry.1 = g := (Prod.mk.injEq ..).mp hpair |>.1
          have hargs_eq : entry.2 = args := (Prod.mk.injEq ..).mp hpair |>.2
          rw [hname_g] at hlook
          rw [hlook] at hdt
          have hdt_eq : templateDt = dt := by
            have := Option.some.inj hdt
            cases this
            rfl
          simp only [Option.some.injEq] at hmono
          -- produce the freshly-pushed newDt
          refine ⟨_, Array.mem_push_self, hmono, ?_⟩
          -- Show constructors match the `MonoShapeOk` shape with `dt` and `args`.
          subst hdt_eq
          rw [hargs_eq]
        · -- key no match → falls through to state.mono
          have := hinv g args g' hmono hdt
          rcases this with ⟨newDt, hmem, hname, hctors⟩
          refine ⟨newDt, ?_, hname, hctors⟩
          exact Array.mem_push_of_mem _ hmem
      · -- throw: lengths differ
        cases hstep
    · -- error case from match: .constructor or none
      cases hstep

/-- Helper: folding `concretizeDrainEntry` over a list preserves `MonoShapeOk`. -/
theorem concretizeDrainEntry_list_foldlM_preserves_MonoShapeOk
    {decls : Typed.Decls}
    (L : List (Global × Array Typ))
    (state0 state' : DrainState)
    (hinv0 : state0.MonoShapeOk decls)
    (hstep : L.foldlM (concretizeDrainEntry decls) state0 = .ok state') :
    state'.MonoShapeOk decls := by
  induction L generalizing state0 with
  | nil =>
    simp only [List.foldlM, pure, Except.pure, Except.ok.injEq] at hstep
    rw [← hstep]
    exact hinv0
  | cons hd tl ih =>
    simp only [List.foldlM, bind, Except.bind] at hstep
    split at hstep
    · cases hstep
    · rename_i s'' hs''
      have hinv1 : s''.MonoShapeOk decls :=
        concretizeDrainEntry_preserves_MonoShapeOk hinv0 hd hs''
      exact ih s'' hinv1 hstep

/-- Helper: `concretizeDrainIter` preserves `MonoShapeOk`. -/
theorem concretizeDrainIter_preserves_MonoShapeOk
    {decls : Typed.Decls} {state state' : DrainState}
    (hinv : state.MonoShapeOk decls)
    (hstep : concretizeDrainIter decls state = .ok state') :
    state'.MonoShapeOk decls := by
  unfold concretizeDrainIter at hstep
  rw [← Array.foldlM_toList] at hstep
  let state0 : DrainState := { state with pending := ∅ }
  have hinv0 : state0.MonoShapeOk decls := hinv
  exact concretizeDrainEntry_list_foldlM_preserves_MonoShapeOk
    state.pending.toArray.toList state0 state' hinv0 hstep

/-- `concretizeDrain` preserves `MonoShapeOk`. -/
theorem concretize_drain_shape_equation
    {decls : Typed.Decls} (fuel : Nat) (init : DrainState)
    (_hinv : init.MonoShapeOk decls)
    {drained : DrainState}
    (_hdrain : concretizeDrain decls fuel init = .ok drained) :
    drained.MonoShapeOk decls := by
  induction fuel generalizing init with
  | zero =>
    unfold concretizeDrain at _hdrain
    by_cases hpen : init.pending.isEmpty
    · simp only [hpen, if_true, pure, Except.pure, Except.ok.injEq] at _hdrain
      rw [← _hdrain]
      exact _hinv
    · simp [hpen] at _hdrain
  | succ n ih =>
    unfold concretizeDrain at _hdrain
    by_cases hpen : init.pending.isEmpty
    · simp only [hpen, if_true, pure, Except.pure, Except.ok.injEq] at _hdrain
      rw [← _hdrain]
      exact _hinv
    · simp only [hpen, if_false, Bool.false_eq_true] at _hdrain
      simp only [bind, Except.bind] at _hdrain
      split at _hdrain
      · cases _hdrain
      · rename_i state' hstate'
        have hinv' : state'.MonoShapeOk decls :=
          concretizeDrainIter_preserves_MonoShapeOk _hinv hstate'
        exact ih state' hinv' _hdrain

/-- After `concretizeBuild`, every `dt ∈ newDataTypes` resolves in the
output decls as a `.dataType newDt` with `newDt.constructors = dt.constructors`
rewritten by `rewriteTyp emptySubst mono`.

Signature fix (red-team finding): the bare `dt ∈ newDataTypes` is insufficient
for the conclusion — `concretizeBuild` composes three insert-folds, and:
* duplicate names within `newDataTypes` would cause the *later* entry to
  overwrite the earlier one (only one can survive at `dt.name`);
* if some `f ∈ newFunctions` has `f.name = dt.name`, the function-insert
  (final fold) overwrites the datatype entry;
* if some `dt' ∈ newDataTypes` has a constructor `c'` with
  `dt'.name.pushNamespace c'.nameHead = dt.name`, the ctor-insert in the
  inner fold overwrites the datatype entry.
The three disjointness hypotheses below rule out these collisions. In
practice `concretize`'s name-mangling (`concretizeName`) guarantees them. -/
theorem concretize_build_registers_mono
    (decls : Typed.Decls) (mono : MonoMap)
    (newFunctions : Array Typed.Function) (newDataTypes : Array DataType)
    (dt : DataType) (hmem : dt ∈ newDataTypes)
    (hDtUnique : ∀ dt' ∈ newDataTypes, dt'.name = dt.name → dt' = dt)
    (hCtorDisjoint : ∀ dt' ∈ newDataTypes, ∀ c' ∈ dt'.constructors,
      dt'.name.pushNamespace c'.nameHead ≠ dt.name)
    (hFnDtDisjoint : ∀ f ∈ newFunctions, f.name ≠ dt.name) :
    ∃ newDt, (concretizeBuild decls mono newFunctions newDataTypes).getByKey dt.name =
      some (.dataType newDt) ∧
    newDt.constructors = dt.constructors.map fun c =>
      { c with argTypes := c.argTypes.map (rewriteTyp (fun _ => none) mono) } := by
  -- Work directly on `concretizeBuild`'s three-fold structure.
  let emptySubst : Global → Option Typ := fun _ => none
  -- `fromSource` is the first fold's output.
  let fromSource : Typed.Decls := decls.pairs.foldl
    (fun acc p =>
      let (key, d) := p
      match d with
      | .function f =>
        if f.params.isEmpty then
          let newInputs := f.inputs.map fun (l, t) => (l, rewriteTyp emptySubst mono t)
          let newOutput := rewriteTyp emptySubst mono f.output
          let newBody := rewriteTypedTerm decls emptySubst mono f.body
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
  -- The rewritten-ctors and expected newDt for `dt`.
  let rewrittenCtorsOf : DataType → List Constructor := fun d =>
    d.constructors.map fun c =>
      { c with argTypes := c.argTypes.map (rewriteTyp emptySubst mono) }
  let expectedNewDt : DataType := { dt with constructors := rewrittenCtorsOf dt }
  refine ⟨expectedNewDt, ?_, rfl⟩
  -- Key lemma: the ctor-fold preserves `getByKey dt.name` (for any value v)
  -- when each ctor key under `dt'.name.pushNamespace _` is distinct from
  -- `dt.name`. Proved by list induction on the ctor list.
  have ctorFold_preserves :
      ∀ (dt' : DataType) (newDt : DataType) (cs : List Constructor) (acc0 : Typed.Decls)
        (v : Option Typed.Declaration),
        acc0.getByKey dt.name = v →
        (∀ c ∈ cs, dt'.name.pushNamespace c.nameHead ≠ dt.name) →
        (cs.foldl
          (fun acc'' c =>
            let cName := dt'.name.pushNamespace c.nameHead
            acc''.insert cName (.constructor newDt c))
          acc0).getByKey dt.name = v := by
    intro dt' newDt cs
    induction cs with
    | nil => intro acc0 v h0 _; simpa using h0
    | cons c cs ih2 =>
      intro acc0 v h0 hne
      simp only [List.foldl_cons]
      apply ih2
      · have hcne : dt'.name.pushNamespace c.nameHead ≠ dt.name :=
          hne c List.mem_cons_self
        have hbeq : (dt'.name.pushNamespace c.nameHead == dt.name) = false := by
          rw [beq_eq_false_iff_ne]; exact hcne
        rw [IndexMap.getByKey_insert_of_beq_false _ _ hbeq]
        exact h0
      · intro c' hc'
        exact hne c' (List.mem_cons_of_mem _ hc')
  -- `withNewDts.getByKey dt.name = some (.dataType expectedNewDt)` via the
  -- `newDataTypes.foldl` fold. Invariant: once we have processed any index with
  -- a dt-name match, the map resolves `dt.name` to `expectedNewDt`; otherwise
  -- the map still agrees with `fromSource`.
  have hWith : (newDataTypes.foldl
      (fun acc dt' =>
        let rewrittenCtors := dt'.constructors.map fun c =>
          { c with argTypes := c.argTypes.map (rewriteTyp emptySubst mono) }
        let newDt : DataType := { dt' with constructors := rewrittenCtors }
        let acc' := acc.insert dt'.name (.dataType newDt)
        rewrittenCtors.foldl
          (fun acc'' c =>
            let cName := dt'.name.pushNamespace c.nameHead
            acc''.insert cName (.constructor newDt c))
          acc')
      fromSource).getByKey dt.name = some (.dataType expectedNewDt) := by
    -- End-state follows from the motive at `i = newDataTypes.size` combined
    -- with `dt ∈ newDataTypes`.
    have hfold := Array.foldl_induction
      (as := newDataTypes)
      (f := fun acc dt' =>
        let rewrittenCtors := dt'.constructors.map fun c =>
          { c with argTypes := c.argTypes.map (rewriteTyp emptySubst mono) }
        let newDt : DataType := { dt' with constructors := rewrittenCtors }
        let acc' := acc.insert dt'.name (.dataType newDt)
        rewrittenCtors.foldl
          (fun acc'' c =>
            let cName := dt'.name.pushNamespace c.nameHead
            acc''.insert cName (.constructor newDt c))
          acc')
      (init := fromSource)
      (motive := fun (i : Nat) (acc : Typed.Decls) =>
        ((∃ (j : Nat) (hj : j < i) (hj' : j < newDataTypes.size),
            (newDataTypes[j]'hj').name = dt.name) →
          acc.getByKey dt.name = some (.dataType expectedNewDt)) ∧
        ((∀ (j : Nat) (hj : j < i) (hj' : j < newDataTypes.size),
            (newDataTypes[j]'hj').name ≠ dt.name) →
          acc.getByKey dt.name = fromSource.getByKey dt.name))
      ?base ?step
    -- Post-fold: use dt ∈ newDataTypes to exhibit a j with matching name.
    · obtain ⟨k, hk_lt, hk_eq⟩ := Array.mem_iff_getElem.mp hmem
      have : ∃ (j : Nat) (hj : j < newDataTypes.size) (hj' : j < newDataTypes.size),
          (newDataTypes[j]'hj').name = dt.name :=
        ⟨k, hk_lt, hk_lt, by rw [hk_eq]⟩
      exact hfold.1 this
    · -- Base case: i = 0, no j < 0.
      refine ⟨?_, ?_⟩
      · rintro ⟨_, h, _, _⟩; exact absurd h (Nat.not_lt_zero _)
      · intro _; rfl
    · -- Step case.
      intro i acc ⟨ihPos, ihNeg⟩
      -- Generalize the `i`-th datatype so the goal uses a fresh `dt'` we can
      -- rewrite against (avoid zeta-reduction of local `let`s).
      generalize hdt'_eq : (newDataTypes[i.val]'i.isLt) = dt'
      -- Recover `dt' ∈ newDataTypes` via the original index.
      have hdt'_mem : dt' ∈ newDataTypes := hdt'_eq ▸ Array.getElem_mem i.isLt
      -- `rctors` and `newDt'` are built from `dt'`.
      let rctors : List Constructor := dt'.constructors.map fun c =>
        { c with argTypes := c.argTypes.map (rewriteTyp emptySubst mono) }
      let newDt' : DataType := { dt' with constructors := rctors }
      -- Each rctor's name is ≠ dt.name when pushed under dt'.name.
      have hrctor_ne : ∀ c ∈ rctors, dt'.name.pushNamespace c.nameHead ≠ dt.name := by
        intro c hc
        simp only [rctors, List.mem_map] at hc
        obtain ⟨c₀, hc₀_mem, hc₀_eq⟩ := hc
        have hname_eq : c.nameHead = c₀.nameHead := by rw [← hc₀_eq]
        rw [hname_eq]
        exact hCtorDisjoint dt' hdt'_mem c₀ hc₀_mem
      -- Split on whether dt'.name = dt.name (i.e., this step is a "dt step").
      by_cases hmatch : dt'.name = dt.name
      · have hdt'_eq_dt : dt' = dt := hDtUnique dt' hdt'_mem hmatch
        have hrctors_eq : rctors = rewrittenCtorsOf dt := by
          show (dt'.constructors.map _) = (dt.constructors.map _)
          rw [hdt'_eq_dt]
        have hnewDt'_eq_expected : newDt' = expectedNewDt := by
          show ({ dt' with constructors := rctors } : DataType) = expectedNewDt
          rw [hdt'_eq_dt]
          show ({ dt with constructors := rctors } : DataType) = expectedNewDt
          show ({ dt with constructors := rctors } : DataType) =
            { dt with constructors := rewrittenCtorsOf dt }
          rw [hrctors_eq]
        refine ⟨?_, ?_⟩
        · intro _
          -- Goal (simp-showable): the step body's result has getByKey dt.name = some expectedNewDt.
          show (rctors.foldl
              (fun acc'' c =>
                let cName := dt'.name.pushNamespace c.nameHead
                acc''.insert cName (.constructor newDt' c))
              (acc.insert dt'.name (.dataType newDt'))).getByKey dt.name =
            some (.dataType expectedNewDt)
          apply ctorFold_preserves dt' newDt' rctors
          · rw [hmatch, ← hnewDt'_eq_expected]
            exact IndexMap.getByKey_insert_self _ _ _
          · exact hrctor_ne
        · intro habs
          have habs_i : (newDataTypes[i.val]'i.isLt).name ≠ dt.name :=
            habs i.val (Nat.lt_succ_self _) i.isLt
          rw [hdt'_eq] at habs_i
          exact absurd hmatch habs_i
      · have hbeq : (dt'.name == dt.name) = false := by
          rw [beq_eq_false_iff_ne]; exact hmatch
        refine ⟨?_, ?_⟩
        · rintro ⟨j, hj, hj', hj_name⟩
          have hprev : acc.getByKey dt.name = some (.dataType expectedNewDt) := by
            by_cases hji : j = i.val
            · subst hji
              -- newDataTypes[j] = dt', and dt'.name = hj_name = dt.name, contradicting hmatch.
              have : dt'.name = dt.name := hdt'_eq ▸ hj_name
              exact absurd this hmatch
            · have hjlt : j < i.val := by omega
              exact ihPos ⟨j, hjlt, hj', hj_name⟩
          show (rctors.foldl
              (fun acc'' c =>
                let cName := dt'.name.pushNamespace c.nameHead
                acc''.insert cName (.constructor newDt' c))
              (acc.insert dt'.name (.dataType newDt'))).getByKey dt.name =
            some (.dataType expectedNewDt)
          apply ctorFold_preserves dt' newDt' rctors
          · rw [IndexMap.getByKey_insert_of_beq_false _ _ hbeq]
            exact hprev
          · exact hrctor_ne
        · intro hall
          have hprev : acc.getByKey dt.name = fromSource.getByKey dt.name := by
            apply ihNeg
            intro j hj hj'
            exact hall j (Nat.lt_succ_of_lt hj) hj'
          show (rctors.foldl
              (fun acc'' c =>
                let cName := dt'.name.pushNamespace c.nameHead
                acc''.insert cName (.constructor newDt' c))
              (acc.insert dt'.name (.dataType newDt'))).getByKey dt.name =
            fromSource.getByKey dt.name
          apply ctorFold_preserves dt' newDt' rctors
          · rw [IndexMap.getByKey_insert_of_beq_false _ _ hbeq]
            exact hprev
          · exact hrctor_ne
  -- Outer `newFunctions.foldl` preserves `getByKey dt.name` since every
  -- `f ∈ newFunctions` has `f.name ≠ dt.name`.
  apply Array.foldl_induction
    (motive := fun (i : Nat) (acc : Typed.Decls) =>
      acc.getByKey dt.name = some (.dataType expectedNewDt))
  · exact hWith
  · intro i acc ih
    let f := newFunctions[i.val]'i.isLt
    have hfmem : f ∈ newFunctions := Array.getElem_mem _
    have hf_name_ne : f.name ≠ dt.name := hFnDtDisjoint f hfmem
    have hbeq : (f.name == dt.name) = false := by
      rw [beq_eq_false_iff_ne]; exact hf_name_ne
    show ((acc.insert f.name (.function _)).getByKey dt.name = some (.dataType expectedNewDt))
    rw [IndexMap.getByKey_insert_of_beq_false _ _ hbeq]
    exact ih

/-! #### Helpers for `concretize_build_excludes_polymorphic` — reverse
key-analysis over `List.foldl` of conditional-insert steps.

Three helpers cover the three folds of `concretizeBuild`:
* `i4_outerStep_bwd` — unconditional insert at `f.name`.
* `i4_midStep_bwd` — insert at `dt.name` then inner ctor-fold of inserts at
  `dt.name.pushNamespace c.nameHead`.
* `i4_innerStep_bwd` — the source-step, with conditional insert guarded by
  `params.isEmpty`. -/

/-- Backward list induction: a fold whose step either preserves the
accumulator or inserts at `p.1` in the map. -/
theorem i4_listFoldl_bwd
    {α : Type _} {γ : Type _} [BEq α] [Hashable α]
    [EquivBEq α] [LawfulHashable α] {β : Type _}
    (step : IndexMap α γ → β → IndexMap α γ)
    (toKey : β → α)
    (hstep : ∀ (acc : IndexMap α γ) (b : β) (g : α),
      (step acc b).containsKey g →
        acc.containsKey g ∨ (toKey b == g) = true)
    (g : α) : ∀ (xs : List β) (init : IndexMap α γ),
      (xs.foldl step init).containsKey g →
        init.containsKey g ∨ ∃ b ∈ xs, (toKey b == g) = true
  | [], _, h => Or.inl h
  | x :: rest, init, h => by
    simp only [List.foldl_cons] at h
    have ih := i4_listFoldl_bwd step toKey hstep g rest (step init x) h
    rcases ih with h1 | ⟨b, hb, hbe⟩
    · rcases hstep init x g h1 with h2 | h2
      · exact Or.inl h2
      · exact Or.inr ⟨x, List.mem_cons_self, h2⟩
    · exact Or.inr ⟨b, List.mem_cons_of_mem _ hb, hbe⟩

/-- Polymorphic source entries are NOT in `monoDecls`.
Every key in `concretizeBuild`'s output either (a) was monomorphic in source
decls (`params.isEmpty`), or (b) came from `newDataTypes`/`newFunctions`. -/
theorem concretize_build_excludes_polymorphic
    (decls : Typed.Decls) (mono : MonoMap)
    (newFunctions : Array Typed.Function) (newDataTypes : Array DataType)
    (key : Global) (d : Typed.Declaration)
    (_hget : (concretizeBuild decls mono newFunctions newDataTypes).getByKey key =
      some d) :
    -- Source origin: monomorphic OR synthesized.
    (∃ srcD, decls.getByKey key = some srcD ∧
      (match srcD with
       | .function f => f.params = []
       | .dataType dt => dt.params = []
       | _ => True)) ∨
    (∃ f ∈ newFunctions, f.name = key) ∨
    (∃ dt ∈ newDataTypes, dt.name = key ∨
      ∃ c ∈ dt.constructors, dt.name.pushNamespace c.nameHead = key) := by
  -- Extract `containsKey key` on the final map.
  have hcontains_final : (concretizeBuild decls mono newFunctions newDataTypes).containsKey key := by
    rw [← IndexMap.getByKey_ne_none_iff_containsKey]; rw [_hget]; exact Option.some_ne_none _
  -- The three step functions, as lambdas.
  let emptySubst : Global → Option Typ := fun _ => none
  let fnStep : Typed.Decls → Typed.Function → Typed.Decls := fun acc f =>
    acc.insert f.name (.function
      { f with
        inputs := f.inputs.map fun (l, t) => (l, rewriteTyp emptySubst mono t),
        output := rewriteTyp emptySubst mono f.output,
        body := rewriteTypedTerm decls emptySubst mono f.body })
  let dtStep : Typed.Decls → DataType → Typed.Decls := fun acc dt =>
    let rewrittenCtors := dt.constructors.map fun c =>
      { c with argTypes := c.argTypes.map (rewriteTyp emptySubst mono) }
    let newDt : DataType := { dt with constructors := rewrittenCtors }
    let acc' := acc.insert dt.name (.dataType newDt)
    rewrittenCtors.foldl
      (fun acc'' c =>
        let cName := dt.name.pushNamespace c.nameHead
        acc''.insert cName (.constructor newDt c))
      acc'
  let srcStep : Typed.Decls → Global × Typed.Declaration → Typed.Decls :=
    fun acc p =>
      let (k, dd) := p
      match dd with
      | .function f =>
        if f.params.isEmpty then
          acc.insert k (.function
            { f with
              inputs := f.inputs.map fun (l, t) => (l, rewriteTyp emptySubst mono t),
              output := rewriteTyp emptySubst mono f.output,
              body := rewriteTypedTerm decls emptySubst mono f.body })
        else acc
      | .dataType dt =>
        if dt.params.isEmpty then
          let newCtors := dt.constructors.map fun c =>
            { c with argTypes := c.argTypes.map (rewriteTyp emptySubst mono) }
          acc.insert k (.dataType { dt with constructors := newCtors })
        else acc
      | .constructor dt c =>
        if dt.params.isEmpty then
          let newArgTypes := c.argTypes.map (rewriteTyp emptySubst mono)
          let newCtor : Constructor := { c with argTypes := newArgTypes }
          let rewrittenCtors := dt.constructors.map fun c' =>
            { c' with argTypes := c'.argTypes.map (rewriteTyp emptySubst mono) }
          let newDt : DataType := { dt with constructors := rewrittenCtors }
          acc.insert k (.constructor newDt newCtor)
        else acc
  let fromSource : Typed.Decls := decls.pairs.toList.foldl srcStep default
  let withNewDts : Typed.Decls := newDataTypes.toList.foldl dtStep fromSource
  have hconc_eq :
      concretizeBuild decls mono newFunctions newDataTypes =
        newFunctions.toList.foldl fnStep withNewDts := by
    show concretizeBuild decls mono newFunctions newDataTypes =
      newFunctions.toList.foldl fnStep (newDataTypes.toList.foldl dtStep
        (decls.pairs.toList.foldl srcStep default))
    show _ = _
    unfold concretizeBuild
    repeat rw [← Array.foldl_toList]
    rfl
  rw [hconc_eq] at hcontains_final
  -- Outer step: unconditional insert at `f.name`.
  have hOuterStep : ∀ (acc : Typed.Decls) (f : Typed.Function) (g : Global),
      (fnStep acc f).containsKey g →
      acc.containsKey g ∨ (f.name == g) = true := by
    intro acc f g hc
    exact (IndexMap.containsKey_insert_iff_or _ _ _ _).mp hc
  have hOuterBwd := i4_listFoldl_bwd fnStep Typed.Function.name hOuterStep key
    newFunctions.toList withNewDts hcontains_final
  rcases hOuterBwd with hcontains_withNewDts | ⟨f, hfmem, hfeq⟩
  · -- Middle step: inner ctor-fold over rewrittenCtors pushed under `dt.name`,
    -- combined with outer insert at `dt.name`. Either key matches dt.name, or
    -- key matches some `dt.name.pushNamespace c.nameHead`, or it was already there.
    -- Helper: inner ctor-fold backward analysis.
    have hCtorFold_bwd :
        ∀ (dt : DataType) (newDt : DataType) (cs : List Constructor) (acc : Typed.Decls),
          (cs.foldl
            (fun acc'' c =>
              let cName := dt.name.pushNamespace c.nameHead
              acc''.insert cName (.constructor newDt c))
            acc).containsKey key →
          acc.containsKey key ∨ ∃ c ∈ cs, dt.name.pushNamespace c.nameHead = key := by
      intro dt newDt cs
      induction cs with
      | nil => intro acc hc; exact Or.inl hc
      | cons c rest ih =>
        intro acc hc
        simp only [List.foldl_cons] at hc
        rcases ih _ hc with h1 | ⟨c'', hc''mem, hc''eq⟩
        · rcases (IndexMap.containsKey_insert_iff_or _ _ _ _).mp h1 with h2 | h2
          · exact Or.inl h2
          · exact Or.inr ⟨c, List.mem_cons_self, LawfulBEq.eq_of_beq h2⟩
        · exact Or.inr ⟨c'', List.mem_cons_of_mem _ hc''mem, hc''eq⟩
    -- Now outer list induction over newDataTypes.toList.
    have hMidBwd : ∀ (xs : List DataType) (init : Typed.Decls),
        (xs.foldl dtStep init).containsKey key →
        init.containsKey key ∨
          ∃ dt ∈ xs, dt.name = key ∨
            ∃ c ∈ dt.constructors, dt.name.pushNamespace c.nameHead = key := by
      intro xs
      induction xs with
      | nil => intro init hc; exact Or.inl hc
      | cons dt rest ih =>
        intro init hc
        simp only [List.foldl_cons] at hc
        rcases ih _ hc with h1 | ⟨dt', hdt'mem, hdt'cond⟩
        · -- h1 : (dtStep init dt).containsKey key
          -- dtStep init dt = (rewrittenCtors.foldl ... (init.insert dt.name (.dataType newDt)))
          -- Apply inner ctor-fold backward.
          let rewrittenCtors := dt.constructors.map fun c =>
            { c with argTypes := c.argTypes.map (rewriteTyp emptySubst mono) }
          let newDt : DataType := { dt with constructors := rewrittenCtors }
          have hc' : (rewrittenCtors.foldl
              (fun acc'' c =>
                let cName := dt.name.pushNamespace c.nameHead
                acc''.insert cName (.constructor newDt c))
              (init.insert dt.name (.dataType newDt))).containsKey key = true := h1
          rcases hCtorFold_bwd dt newDt rewrittenCtors _ hc' with h2 | ⟨c, hcmem, hceq⟩
          · rcases (IndexMap.containsKey_insert_iff_or _ _ _ _).mp h2 with h3 | h3
            · exact Or.inl h3
            · exact Or.inr ⟨dt, List.mem_cons_self,
                Or.inl (LawfulBEq.eq_of_beq h3)⟩
          · -- c ∈ rewrittenCtors: find original constructor with same nameHead.
            have : ∃ c' ∈ dt.constructors, c'.nameHead = c.nameHead := by
              simp only [List.mem_map, rewrittenCtors] at hcmem
              obtain ⟨c', hc'mem, hc'eq⟩ := hcmem
              exact ⟨c', hc'mem, by rw [← hc'eq]⟩
            obtain ⟨c', hc'mem, hc'nameHead⟩ := this
            right
            refine ⟨dt, List.mem_cons_self, Or.inr ⟨c', hc'mem, ?_⟩⟩
            rw [hc'nameHead]; exact hceq
        · exact Or.inr ⟨dt', List.mem_cons_of_mem _ hdt'mem, hdt'cond⟩
    rcases hMidBwd newDataTypes.toList fromSource hcontains_withNewDts with
      hcontains_fromSource | ⟨dt, hdtmem, hdtcond⟩
    · -- Innermost: key is in fromSource ⇒ source entry is monomorphic.
      -- srcStep is a conditional insert. Use i4_listFoldl_bwd with a stronger
      -- hypothesis that also exposes the `params = []` condition.
      have hSrcStep : ∀ (acc : Typed.Decls) (p : Global × Typed.Declaration) (g : Global),
          (srcStep acc p).containsKey g →
          acc.containsKey g ∨ ((p.1 == g) = true ∧
            (match p.2 with
             | .function f => f.params = []
             | .dataType dt => dt.params = []
             | _ => True)) := by
        intro acc p g hc
        obtain ⟨k, dd⟩ := p
        -- `srcStep` reduces to the match under `(k, dd)`; `hc`'s type is already
        -- in that form.  Unfold `srcStep` to expose the match.
        simp only [srcStep] at hc
        cases dd with
        | function f =>
          by_cases hp : f.params.isEmpty = true
          · simp only [hp, if_true] at hc
            rcases (IndexMap.containsKey_insert_iff_or _ _ _ _).mp hc with h | h
            · exact Or.inl h
            · right
              refine ⟨h, ?_⟩
              show f.params = []
              cases hfp : f.params with
              | nil => rfl
              | cons _ _ => rw [hfp] at hp; cases hp
          · simp only [hp, if_false, Bool.false_eq_true] at hc
            exact Or.inl hc
        | dataType dt =>
          by_cases hp : dt.params.isEmpty = true
          · simp only [hp, if_true] at hc
            rcases (IndexMap.containsKey_insert_iff_or _ _ _ _).mp hc with h | h
            · exact Or.inl h
            · right
              refine ⟨h, ?_⟩
              show dt.params = []
              cases hdp : dt.params with
              | nil => rfl
              | cons _ _ => rw [hdp] at hp; cases hp
          · simp only [hp, if_false, Bool.false_eq_true] at hc
            exact Or.inl hc
        | constructor dt c =>
          by_cases hp : dt.params.isEmpty = true
          · simp only [hp, if_true] at hc
            rcases (IndexMap.containsKey_insert_iff_or _ _ _ _).mp hc with h | h
            · exact Or.inl h
            · exact Or.inr ⟨h, trivial⟩
          · simp only [hp, if_false, Bool.false_eq_true] at hc
            exact Or.inl hc
      -- List induction.
      have hSrcBwd : ∀ (pairs : List (Global × Typed.Declaration)) (init : Typed.Decls),
          (pairs.foldl srcStep init).containsKey key →
          init.containsKey key ∨ ∃ p ∈ pairs, (p.1 == key) = true ∧
            (match p.2 with
             | .function f => f.params = []
             | .dataType dt => dt.params = []
             | _ => True) := by
        intro pairs
        induction pairs with
        | nil => intro init hc; exact Or.inl hc
        | cons x rest ih =>
          intro init hc
          simp only [List.foldl_cons] at hc
          rcases ih _ hc with h1 | ⟨p, hpm, hpe, hcond⟩
          · rcases hSrcStep init x key h1 with h2 | ⟨h2, hcond⟩
            · exact Or.inl h2
            · exact Or.inr ⟨x, List.mem_cons_self, h2, hcond⟩
          · exact Or.inr ⟨p, List.mem_cons_of_mem _ hpm, hpe, hcond⟩
      rcases hSrcBwd decls.pairs.toList default hcontains_fromSource with
        habsurd | ⟨p, hpm, hpe, hcond⟩
      · exfalso
        have := IndexMap.containsKey_default (α := Global) (β := Typed.Declaration) key
        rw [this] at habsurd
        cases habsurd
      · left
        have hkey_eq : p.1 = key := LawfulBEq.eq_of_beq hpe
        refine ⟨p.2, ?_, hcond⟩
        have := IndexMap.getByKey_of_mem_pairs decls p.1 p.2
          (by rcases p with ⟨a, b⟩; exact hpm)
        rw [hkey_eq] at this; exact this
    · exact Or.inr (Or.inr ⟨dt, Array.mem_toList_iff.mp hdtmem, hdtcond⟩)
  · refine Or.inr (Or.inl ?_)
    exact ⟨f, Array.mem_toList_iff.mp hfmem, LawfulBEq.eq_of_beq hfeq⟩

-- `concretize_mono_closed` DELETED: vacuous as stated. `AppReachable` was
-- defined as `| _, _, _ => True`, so the hypothesis reduced to
-- `decls.pairs ≠ []` and the conclusion `drained.mono.contains (g, args)`
-- is false for arbitrary `(g, args)`. Re-introduce only with a real
-- reachability predicate (e.g. a `collectAppsInDecl` fold) once the
-- concretize worklist invariant is stated precisely.

-- `concretizeName_injective` DELETED: it was FALSE as stated.
-- Counterexample: `concretizeName "A" #[.field] = "A.G" = concretizeName "A.G" #[]`.
-- `appendNameLimbs` builds by `pushNamespace` which collides between
-- "extend template" vs "encode arg" forms. Cannot be repaired without a
-- structural separator/marker in the encoding scheme.

/-- For empty args, `concretizeName g #[] = g`. Identity mangling
on monomorphic (0-argument) instantiations. -/
theorem concretizeName_empty_args (g : Global) :
    concretizeName g #[] = g := by
  unfold concretizeName
  rfl

-- `Concrete.Typ.FirstOrder`, `Concrete.Decls.FirstOrderReturn`,
-- `Concrete.Typ.RefClosed`, `Concrete.Declaration.RefClosed`,
-- `Concrete.Decls.RefClosed`, `Concrete.Term.RefsDt`, `Concrete.Decls.TermRefsDt`
-- moved to `Ix/Aiur/Semantics/ConcreteInvariants.lean`.

-- `concretize_preserves_TermRefsDt` lives further down, AFTER the
-- `rewriteTypedTerm_preserves_RefsDt` and `termToConcrete_preserves_RefsDt`
-- infrastructure, which sit alongside the FO chain so they can share
-- helpers (`mem_of_attach_map`, `Array.mem_mapM_ok_forall`).


end Aiur

end -- public section
