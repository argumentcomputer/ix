module
public import Ix.Aiur.Compiler.Concretize
public import Ix.Aiur.Compiler.Lower
public import Ix.Aiur.Proofs.ConcretizeProgress
public import Ix.Aiur.Proofs.CheckSound
public import Ix.Aiur.Proofs.ConcreteEvalInversion
public import Ix.Aiur.Proofs.ValueEqFlatten
public import Ix.Aiur.Semantics.WellFormed
public import Ix.Aiur.Semantics.ConcreteEval
public import Ix.Aiur.Semantics.SourceEval
public import Ix.Aiur.Semantics.Relation
public import Ix.Aiur.Semantics.Flatten
public import Ix.Aiur.Semantics.DrainInvariants
public import Ix.Aiur.Semantics.ConcreteInvariants

/-!
Concretize soundness.

Preservation: `substInTypedTerm subst body` has the same value denotation as
`body` under the original type environment. Values are type-erased; substitution
changes types but not value denotation.

Progress: the termination check (rejecting polymorphic recursion) bounds the
worklist; termination follows by structural induction on the type-argument DAG.
-/

public section

namespace Aiur

/-! ## `typFlatSize` preservation through concretize's type rewrites

These theorems capture a structural fact about `concretize`'s type rewrites:
`rewriteTyp emptySubst mono` preserves `typFlatSize` on `MvarFree` types whose
`.app` heads are in `mono`. They are sorried here because a full proof requires
induction over `Typ` + `DataType` mutual recursion paralleling `typFlatSizeBound`
+ `dataTypeFlatSizeBound`. See `StructCompatible.lean` for the downstream
consumer (`compile_ok_input_layout_matches`). -/

/-! ### `typFlatSize` preservation across `concretize`.

The earlier `MonoCompatible` predicate was stated on source `decls` with
`.ref g'` expected to resolve there — but `g' = concretizeName g args` is
fresh, never in source decls, so the predicate was provably false for any
non-trivial polymorphic program. Additionally, `typFlatSizeBound`'s `.app`
arm ignores `args` (single `g`-lookup), making the equation self-contradictory
for templates with multiple instantiations.

The correct formulation lives across TWO decls tables: source decls for the
pre-rewrite side, mono decls (post-concretize Step 3) for the rewritten side.
Empty `visited` is sufficient — the downstream caller
(`compile_ok_input_layout_matches`) only invokes at the outer entry.

-/

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
private theorem concretizeDrainEntry_preserves_MonoHasDecl
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
private theorem concretizeDrainEntry_list_foldlM_preserves_MonoHasDecl
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
private theorem concretizeDrainIter_preserves_MonoHasDecl
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
private theorem concretizeDrainEntry_preserves_MonoShapeOk
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
private theorem concretizeDrainEntry_list_foldlM_preserves_MonoShapeOk
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
private theorem concretizeDrainIter_preserves_MonoShapeOk
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
private theorem i4_listFoldl_bwd
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

/-! ### `FnFreeBody` — ported body of `runFunction_preserves_FnFree`.

Ported from `Ix/Aiur/Proofs/FnFreeBodyScratch.lean` 2026-04-24. Houses the
consolidated infrastructure sorry together with the small FnFree lemmas and
the `ref_arm_FnFree` discharger that exercises `TermRefsDt`. The real theorem
below delegates its body to `FnFreeBody.runFunction_preserves_FnFree_body`. -/
private def _fnFreeBody_docstub : Unit := ()

namespace FnFreeBody

open Concrete.Eval

/-! #### Small FnFree lemmas used by the trivial arms. -/

/-- FnFree cannot inhabit `.fn _`. -/
theorem FnFree_not_fn (g : Global) : ¬ Value.FnFree (.fn g) := fun h => nomatch h

/-- A unit-tuple value (two fields) is FnFree. -/
theorem FnFree_two_field_tuple (a b : G) :
    Value.FnFree (.tuple #[.field a, .field b]) := by
  refine .tuple ?_
  intro v hv
  simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl
  · exact .field _
  · exact .field _

/-- An array of `n` field values is FnFree. -/
theorem FnFree_ofFn_field (n : Nat) (f : Fin n → G) :
    Value.FnFree (.array (Array.ofFn fun (i : Fin n) => .field (f i))) := by
  refine .array ?_
  intro v hv
  rw [Array.mem_ofFn] at hv
  obtain ⟨i, hi⟩ := hv
  subst hi
  exact .field _

/-- Bindings-FnFree invariant. Every bound value is `FnFree`. -/
def BindingsFnFree (bindings : Bindings) : Prop :=
  ∀ p ∈ bindings, Value.FnFree p.2

theorem BindingsFnFree.nil : BindingsFnFree [] := by
  intro p hp; cases hp

theorem BindingsFnFree.cons {l : Local} {v : Value} {bs : Bindings}
    (hv : Value.FnFree v) (hbs : BindingsFnFree bs) :
    BindingsFnFree ((l, v) :: bs) := by
  intro p hp
  cases hp
  · exact hv
  · rename_i hp'; exact hbs _ hp'

theorem BindingsFnFree.append {bs₁ bs₂ : Bindings}
    (h₁ : BindingsFnFree bs₁) (h₂ : BindingsFnFree bs₂) :
    BindingsFnFree (bs₁ ++ bs₂) := by
  intro p hp
  rw [List.mem_append] at hp
  cases hp with
  | inl hp => exact h₁ _ hp
  | inr hp => exact h₂ _ hp

/-- Projection through `Bindings.find? (·.1 == l)`. -/
theorem BindingsFnFree.find?_FnFree {bs : Bindings} {l : Local} {v : Value}
    (hbs : BindingsFnFree bs)
    (hfind : bs.find? (·.1 == l) = some (l, v)) :
    Value.FnFree v := by
  have hmem := List.mem_of_find?_eq_some hfind
  exact hbs _ hmem

/-! #### `.ref` arm: closed under `TermRefsDt`. -/

/-- Under `TermRefsDt`, evaluating a top-level `.ref g` subterm that appears in
a function body succeeds only at `.ctor g #[]` (zero-arg constructor). Any
other successful shape would require `cd.getByKey g = some (.function _)`,
which `TermRefsDt` rules out at the bound `.ref` node.

This captures the sig-strengthening rationale for the `.ref` arm of the
mutual-induction heart. -/
theorem ref_arm_FnFree
    (cd : Concrete.Decls) (fuel : Nat) (bindings : Bindings)
    (typ : Concrete.Typ) (e : Bool) (g : Global)
    (st : EvalState) (v : Value) (st' : EvalState)
    (hdt : (∃ dt, cd.getByKey g = some (.dataType dt)) ∨
           (∃ dt c, cd.getByKey g = some (.constructor dt c)))
    (heval : Concrete.Eval.interp cd fuel bindings (.ref typ e g) st = .ok (v, st')) :
    Value.FnFree v := by
  unfold Concrete.Eval.interp at heval
  -- Discriminate by `cd.getByKey g` via `TermRefsDt` (rules out `.function`).
  split at heval
  · -- `.function` branch — ruled out by TermRefsDt
    rename_i heq
    rcases hdt with ⟨_, hdt⟩ | ⟨_, _, hctor⟩
    · rw [hdt] at heq; cases heq
    · rw [hctor] at heq; cases heq
  · -- `.constructor` branch → splits on `c.argTypes.isEmpty`
    rename_i ctor heq
    split at heval
    · -- empty-arg constructor — yields `.ctor g #[]`
      injection heval with hpair
      injection hpair with hv
      subst hv
      refine .ctor g ?_
      intro x hx
      simp at hx
    · cases heval
  · cases heval  -- `.dataType` branch → error
  · cases heval  -- `none` branch → error

/-! #### Auxiliary: `unflattenValue` produces FnFree (modulo function types).

`unflattenValueBound` is called with `(default : Source.Decls)` (size 0, so
bound = 1) at every `.letLoad`/`.load` site. Under empty decls:

* `.unit`/`.field`/`.pointer`/`.ref`/`.app`: terminal (don't recurse), produce
  `.unit`/`.field`/`.pointer`/`.field`/`.field` — all FnFree.
* `.tuple`/`.array`: recurse with `bound = 0` (so each inner call returns
  `(.unit, 0)`) — everything FnFree.
* `.function`: returns `(.fn ⟨.anonymous⟩, 1)` — NOT FnFree.
* `.mvar _`: returns `(.unit, 0)` — FnFree.

So we need `t ≠ .function _ _` at the OUTER call. The `letLoad`/`load` arms'
`dstTyp` / `t.typ` are `Concrete.Typ`, which `concreteTypToSource` converts
spine-by-spine. The non-`.function` shape is preserved.

For the leaf-arm closure of S1 the strict result we need is: `unflattenValue
(default : Source.Decls) gs offset (concreteTypToSource τ) |>.1 |> Value.FnFree`
under the precondition `τ ≠ .function _ _`. -/

/-- `Concrete.Typ` shape predicate ruling out function types ANYWHERE in the
spine (recursively). The `unflattenValue` aux produces FnFree only when this
holds (any function leaf would unflatten to `.fn _`). -/
inductive NotFunctionTyp : Concrete.Typ → Prop
  | unit : NotFunctionTyp .unit
  | field : NotFunctionTyp .field
  | ref (g) : NotFunctionTyp (.ref g)
  | tuple {ts} (h : ∀ t ∈ ts, NotFunctionTyp t) : NotFunctionTyp (.tuple ts)
  | array {t n} (h : NotFunctionTyp t) : NotFunctionTyp (.array t n)
  | pointer {t} (h : NotFunctionTyp t) : NotFunctionTyp (.pointer t)

/-- `Aiur.Typ` analogue, recursive form. -/
inductive NotFunctionATyp : Aiur.Typ → Prop
  | unit : NotFunctionATyp .unit
  | field : NotFunctionATyp .field
  | ref (g) : NotFunctionATyp (.ref g)
  | app (g a) : NotFunctionATyp (.app g a)
  | mvar (n) : NotFunctionATyp (.mvar n)
  | tuple {ts} (h : ∀ t ∈ ts, NotFunctionATyp t) : NotFunctionATyp (.tuple ts)
  | array {t n} (h : NotFunctionATyp t) : NotFunctionATyp (.array t n)
  | pointer {t} (h : NotFunctionATyp t) : NotFunctionATyp (.pointer t)

theorem NotFunctionATyp_concreteTypToSource :
    ∀ {τ : Concrete.Typ},
    NotFunctionTyp τ →
    NotFunctionATyp (concreteTypToSource τ)
  | .unit, _ => by rw [concreteTypToSource]; exact .unit
  | .field, _ => by rw [concreteTypToSource]; exact .field
  | .ref g, _ => by rw [concreteTypToSource]; exact .ref g
  | .tuple ts, h => by
    cases h with
    | tuple hts =>
      rw [concreteTypToSource]
      refine .tuple ?_
      intro t' ht'
      rw [Array.mem_iff_getElem] at ht'
      obtain ⟨i, hi, heq⟩ := ht'
      rw [Array.size_map, Array.size_attach] at hi
      have hmem : ts[i]'hi ∈ ts := Array.getElem_mem hi
      rw [Array.getElem_map, Array.getElem_attach] at heq
      rw [← heq]
      exact NotFunctionATyp_concreteTypToSource (hts _ hmem)
  | .array t _, h => by
    cases h with
    | array h =>
      rw [concreteTypToSource]
      exact .array (NotFunctionATyp_concreteTypToSource h)
  | .pointer t, h => by
    cases h with
    | pointer h =>
      rw [concreteTypToSource]
      exact .pointer (NotFunctionATyp_concreteTypToSource h)
  | .function _ _, h => by cases h
termination_by τ _ => sizeOf τ
decreasing_by
  all_goals first
    | (have hsm := Array.sizeOf_lt_of_mem hmem; grind)
    | decreasing_tactic

/-- `(default : Source.Decls).getByKey g = none` for any `g`. The default
IndexMap has no entries. -/
private theorem default_Source_Decls_getByKey (g : Global) :
    (default : Source.Decls).getByKey g = none := by
  unfold IndexMap.getByKey
  simp only [default]
  show (do let x ← (∅ : Std.HashMap Global Nat)[g]?
           Option.map Prod.snd (#[] : Array (Global × Source.Declaration))[x]?) = none
  rw [Std.HashMap.getElem?_empty]
  rfl

/-- `unflattenValueBound (default : Source.Decls) gs bound offset t |>.1 |>
Value.FnFree` whenever the Typ tree contains no `.function _ _` anywhere.

Structural induction on `bound` (0 → `.unit`; succ → per-Typ dispatch). The
`.ref` / `.app` arms collapse to `.field` because `default.getByKey g = none`.
`.tuple` and `.array` arms recurse with the IH at smaller `bound`, using the
recursive `NotFunctionATyp`. -/
theorem unflattenValueBound_FnFree
    (gs : Array G) (bound : Nat) :
    ∀ (offset : Nat) (t : Aiur.Typ),
    NotFunctionATyp t →
    Value.FnFree (unflattenValueBound (default : Source.Decls) gs bound offset t).1 := by
  induction bound with
  | zero =>
    intro offset t _hNF
    unfold unflattenValueBound
    exact .unit
  | succ b ih =>
    intro offset t hNF
    cases t with
    | unit =>
      unfold unflattenValueBound
      exact .unit
    | field =>
      unfold unflattenValueBound
      exact .field _
    | pointer t' =>
      unfold unflattenValueBound
      exact .pointer _ _
    | function _ _ => cases hNF
    | mvar _ =>
      unfold unflattenValueBound
      exact .unit
    | tuple ts =>
      unfold unflattenValueBound
      simp only
      refine .tuple ?_
      cases hNF with
      | tuple htsNF =>
        apply Array.foldl_induction
          (motive := fun (_i : Nat) (acc : Array Value × Nat) =>
            ∀ p ∈ acc.1, Value.FnFree p)
        · intro p hp; simp at hp
        · intro i acc hacc p hp
          -- ts.attach[i] : { x // x ∈ ts }; its .val is some ts elt.
          have hatt_mem : (ts.attach[i.val]).val ∈ ts := (ts.attach[i.val]).property
          rw [Array.mem_push] at hp
          cases hp with
          | inl hin => exact hacc _ hin
          | inr heq =>
            subst heq
            exact ih _ _ (htsNF _ hatt_mem)
    | array t' n =>
      unfold unflattenValueBound
      simp only
      refine .array ?_
      intro v hv
      rw [Array.mem_iff_getElem] at hv
      obtain ⟨i, hi, heq⟩ := hv
      rw [Array.size_ofFn] at hi
      rw [Array.getElem_ofFn] at heq
      cases hNF with
      | array hNFt' =>
        rw [← heq]
        exact ih _ t' hNFt'
    | ref g =>
      unfold unflattenValueBound
      simp only [default_Source_Decls_getByKey]
      exact .field _
    | app g args =>
      unfold unflattenValueBound
      simp only [default_Source_Decls_getByKey]
      exact .field _

/-- Outer interface: `unflattenValue` is `unflattenValueBound` at
`decls.size + 1`, here `(default : Source.Decls).size + 1 = 1`. -/
theorem unflattenValue_FnFree
    (gs : Array G) (offset : Nat) (t : Aiur.Typ)
    (hNF : NotFunctionATyp t) :
    Value.FnFree (unflattenValue (default : Source.Decls) gs offset t).1 := by
  unfold unflattenValue
  exact unflattenValueBound_FnFree gs _ offset t hNF

/-! #### Mutual-induction: per-fuel preservation of `FnFree`.

Six theorems, one per interp-family function. Termination uses the same
`(fuel, role, sizeOf t, ...)` lex measure as the eval functions, so the
mutual recursion type-checks identically.

For per-arm closure status see the `interp_FnFree` body: 30+ arms F=0
(unit/var/field/ref/letVar/letWild/ret/tuple/array/match/proj/get/slice/set/
add/sub/mul/eqZero/store/ptrVal/assertEq/u8*/u32LessThan/debug/ioGetInfo/
ioSetInfo/ioRead/ioWrite/app); 2 arms F=1 with sub-sorry citing
`unflattenValue_FnFree` (`letLoad`, `load`). -/

set_option maxHeartbeats 800000 in
mutual

/-- Preservation through `applyGlobal`. -/
theorem applyGlobal_FnFree (cd : Concrete.Decls)
    (_hFOR : Concrete.Decls.FirstOrderReturn cd)
    (_hRefClosed : Concrete.Decls.RefClosed cd)
    (_hTermRefsDt : Concrete.Decls.TermRefsDt cd)
    (fuel : Nat) (g : Global) (args : List Value) (st : EvalState)
    (hargs : ∀ v ∈ args, Value.FnFree v)
    (v : Value) (st' : EvalState)
    (hcall : Concrete.Eval.applyGlobal cd fuel g args st = .ok (v, st')) :
    Value.FnFree v := by
  cases fuel with
  | zero =>
    unfold Concrete.Eval.applyGlobal at hcall
    cases hcall
  | succ n =>
    unfold Concrete.Eval.applyGlobal at hcall
    split at hcall
    · -- `.function f` branch
      rename_i f hfg
      split at hcall
      · cases hcall  -- arity mismatch error
      · -- recurse into `interp` on `f.body` with bindings from `args`
        rename_i _hsize
        have hbindings_FnFree :
            BindingsFnFree (f.inputs.map (·.1) |>.zip args) := by
          -- p ∈ zip xs ys ⇒ p.2 ∈ ys (zip preserves elements pointwise).
          have hzip_snd_mem :
              ∀ {α β} (xs : List α) (ys : List β) (p : α × β),
                p ∈ xs.zip ys → p.2 ∈ ys := by
            intro α β xs
            induction xs with
            | nil => intro ys p hp; simp [List.zip] at hp
            | cons x xs ih =>
              intro ys p hp
              cases ys with
              | nil => simp [List.zip] at hp
              | cons a as =>
                simp only [List.zip_cons_cons, List.mem_cons] at hp
                rcases hp with hp | hp
                · subst hp; exact List.mem_cons_self
                · exact List.mem_cons_of_mem _ (ih as p hp)
          intro p hp
          exact hargs _ (hzip_snd_mem _ _ p hp)
        have htermRefsDt : Concrete.Term.RefsDt cd f.body := _hTermRefsDt _ _ hfg
        exact interp_FnFree cd _hFOR _hRefClosed _hTermRefsDt n
          (f.inputs.map (·.1) |>.zip args) f.body st hbindings_FnFree htermRefsDt
          v st' hcall
    · -- `.constructor` branch — yields `.ctor g args.toArray`
      rename_i _ _ _hfg
      injection hcall with hpair
      injection hpair with hv _
      subst hv
      refine .ctor g ?_
      intro x hx
      rw [Array.mem_toArray] at hx
      exact hargs _ hx
    · cases hcall  -- `none` → error
    · cases hcall  -- `.dataType` → error
termination_by (fuel, 0, 0, 0)

/-- Preservation through `applyLocal`. -/
theorem applyLocal_FnFree (cd : Concrete.Decls)
    (_hFOR : Concrete.Decls.FirstOrderReturn cd)
    (_hRefClosed : Concrete.Decls.RefClosed cd)
    (_hTermRefsDt : Concrete.Decls.TermRefsDt cd)
    (fuel : Nat) (vCallee : Value) (args : List Value) (st : EvalState)
    (hCallee : Value.FnFree vCallee)
    (_hargs : ∀ v ∈ args, Value.FnFree v)
    (v : Value) (st' : EvalState)
    (hcall : Concrete.Eval.applyLocal cd fuel vCallee args st = .ok (v, st')) :
    Value.FnFree v := by
  unfold Concrete.Eval.applyLocal at hcall
  cases vCallee with
  | unit => cases hcall
  | field _ => cases hcall
  | tuple _ => cases hcall
  | array _ => cases hcall
  | ctor _ _ => cases hcall
  | fn g =>
    -- vCallee = .fn g, but hCallee : Value.FnFree (.fn g) is False.
    exact (FnFree_not_fn g hCallee).elim
  | pointer _ _ => cases hcall
termination_by (fuel, 1, 0, 0)

/-- Preservation through `interp`. ~37-arm dispatch. Most arms close F=0 via
inversion lemmas + the per-function IH on the corresponding sub-pieces. -/
theorem interp_FnFree (cd : Concrete.Decls)
    (_hFOR : Concrete.Decls.FirstOrderReturn cd)
    (_hRefClosed : Concrete.Decls.RefClosed cd)
    (_hTermRefsDt : Concrete.Decls.TermRefsDt cd)
    (fuel : Nat) (bindings : Bindings) (t : Concrete.Term) (st : EvalState)
    (hb : BindingsFnFree bindings)
    (htRefsDt : Concrete.Term.RefsDt cd t)
    (v : Value) (st' : EvalState)
    (heval : Concrete.Eval.interp cd fuel bindings t st = .ok (v, st')) :
    Value.FnFree v := by
  -- 37-arm dispatch via `cases t`, with inversion-lemma rewrites + IH calls.
  -- Most arms close F=0; recursive ones use the corresponding sibling theorem
  -- in this mutual block (decreasing on `sizeOf t`).
  cases t with
  | unit τ e =>
    -- LEAF: produces .unit
    rw [Concrete.Eval.interp_unit] at heval
    injection heval with hpair
    injection hpair with hv
    subst hv
    exact .unit
  | var τ e l =>
    -- LEAF: bindings lookup
    rw [Concrete.Eval.interp_var] at heval
    cases hfind : bindings.find? (·.1 == l) with
    | none => rw [hfind] at heval; cases heval
    | some lv =>
      rw [hfind] at heval
      obtain ⟨l', vBound⟩ := lv
      injection heval with hpair
      injection hpair with hv
      subst hv
      -- Need l' = l: from `find?_eq_some` predicate. Mem in bindings.
      have hmem : (l', vBound) ∈ bindings := List.mem_of_find?_eq_some hfind
      exact hb _ hmem
  | field τ e g =>
    -- LEAF
    rw [Concrete.Eval.interp_field] at heval
    injection heval with hpair
    injection hpair with hv
    subst hv
    exact .field g
  | ref τ e g =>
    -- LEAF: closed via ref_arm_FnFree using _hTermRefsDt.
    cases htRefsDt with
    | ref hdt => exact ref_arm_FnFree cd fuel bindings τ e g st v st' hdt heval
  | ret τ e r =>
    -- IH(r)
    rw [Concrete.Eval.interp_ret] at heval
    cases htRefsDt with
    | ret hr =>
      exact interp_FnFree cd _hFOR _hRefClosed _hTermRefsDt fuel bindings r st
        hb hr v st' heval
  | tuple τ e ts =>
    -- IH via evalList_FnFree
    rw [Concrete.Eval.interp_tuple] at heval
    cases hres : Concrete.Eval.evalList cd fuel bindings ts.toList st with
    | error err => rw [hres] at heval; cases heval
    | ok pair =>
      obtain ⟨vs, st''⟩ := pair
      rw [hres] at heval
      injection heval with hpair
      injection hpair with hv
      subst hv
      cases htRefsDt with
      | tuple h =>
        have hts_refs : ∀ t' ∈ ts.toList, Concrete.Term.RefsDt cd t' := by
          intro t' ht'
          exact h t' (Array.mem_toList_iff.mp ht')
        refine .tuple ?_
        intro w hw
        exact evalList_FnFree cd _hFOR _hRefClosed _hTermRefsDt fuel bindings
          ts.toList st hb hts_refs vs st'' hres w hw
  | array τ e ts =>
    -- IH via evalList_FnFree
    rw [Concrete.Eval.interp_array] at heval
    cases hres : Concrete.Eval.evalList cd fuel bindings ts.toList st with
    | error err => rw [hres] at heval; cases heval
    | ok pair =>
      obtain ⟨vs, st''⟩ := pair
      rw [hres] at heval
      injection heval with hpair
      injection hpair with hv
      subst hv
      cases htRefsDt with
      | array h =>
        have hts_refs : ∀ t' ∈ ts.toList, Concrete.Term.RefsDt cd t' := by
          intro t' ht'
          exact h t' (Array.mem_toList_iff.mp ht')
        refine .array ?_
        intro w hw
        exact evalList_FnFree cd _hFOR _hRefClosed _hTermRefsDt fuel bindings
          ts.toList st hb hts_refs vs st'' hres w hw
  | letVar τ e l vT b =>
    -- IH(vT) → val-FnFree → BindingsFnFree.cons → IH(b)
    unfold Concrete.Eval.interp at heval
    split at heval
    · cases heval
    · rename_i val sval hres
      cases htRefsDt with
      | letVar hv hb' =>
        have hval : Value.FnFree val :=
          interp_FnFree cd _hFOR _hRefClosed _hTermRefsDt fuel bindings vT st
            hb hv val sval hres
        have hb_ext : BindingsFnFree ((l, val) :: bindings) :=
          BindingsFnFree.cons hval hb
        exact interp_FnFree cd _hFOR _hRefClosed _hTermRefsDt fuel ((l, val) :: bindings)
          b sval hb_ext hb' v st' heval
  | letWild τ e vT b =>
    unfold Concrete.Eval.interp at heval
    split at heval
    · cases heval
    · rename_i val sval _hres
      cases htRefsDt with
      | letWild _hv hb' =>
        exact interp_FnFree cd _hFOR _hRefClosed _hTermRefsDt fuel bindings b sval
          hb hb' v st' heval
  | letLoad τ e dst dstTyp src b =>
    -- BLOCKED on SD-LoadType: `dstTyp` is unconstrained by `RefsDt`/`RefClosed`/
    -- `FirstOrderReturn`. If `dstTyp = .function _ _`, then
    -- `unflattenValue default gs 0 (concreteTypToSource dstTyp) = (.fn _, 1)`
    -- is NOT FnFree — counterexample to closing this arm without sig-strengthen.
    --
    -- Closure path:
    -- 1. Add `Concrete.Term.TypesNotFunction cd : Concrete.Term → Prop` predicate
    --    constraining each constructor's type-arg (and recursively for
    --    `tuple`/`array` element types via the `Concrete.Typ` spine).
    -- 2. Add `_hTypesNotFunction : Concrete.Decls.TypesNotFunction cd` to
    --    interp_FnFree's sig and propagate through every arm.
    -- 3. Prove `concretize_preserves_TypesNotFunction` (mirror of
    --    `concretize_preserves_TermRefsDt`, ~150-300 LoC propagation chain).
    -- 4. Discharge `compile_correct`'s wrapper via WellFormed-derived obligation.
    -- 5. Strengthen `unflattenValueBound_FnFree`'s tuple/array arms with a
    --    recursive `NotFunctionATyp` predicate to close those F=1.
    --
    -- Once SD-LoadType lands: this arm closes via
    --   `interp_letLoad` → bindings.find? → .pointer → storeLookup → unflattenValue
    --   → `unflattenValue_FnFree` (with NotFunctionATyp witness from
    --      TypesNotFunction at the letLoad node)
    --   → BindingsFnFree.cons → IH(b).
    rw [Concrete.Eval.interp_letLoad] at heval
    sorry
  | «match» τ e scrutIdx cases defaultOpt =>
    -- Bindings lookup → evalMatchCases_FnFree.
    unfold Concrete.Eval.interp at heval
    split at heval
    · cases heval
    · rename_i lvar scrut hfind
      have hscrut : Value.FnFree scrut := by
        have hmem := List.mem_of_find?_eq_some hfind
        exact hb _ hmem
      cases htRefsDt with
      | «match» hcases hdef =>
        exact evalMatchCases_FnFree cd _hFOR _hRefClosed _hTermRefsDt fuel bindings st
          scrut cases defaultOpt 0 hb hscrut hcases hdef v st' heval
  | app τ e g argTms u =>
    -- evalList_FnFree on argTms → applyLocal_FnFree / applyGlobal_FnFree
    rw [Concrete.Eval.interp_app] at heval
    cases hresArgs : Concrete.Eval.evalList cd fuel bindings argTms st with
    | error err => rw [hresArgs] at heval; cases heval
    | ok pair =>
      obtain ⟨argVs, sArgs⟩ := pair
      rw [hresArgs] at heval
      cases htRefsDt with
      | app hargs =>
        have hargVs_FnFree : ∀ w ∈ argVs, Value.FnFree w :=
          evalList_FnFree cd _hFOR _hRefClosed _hTermRefsDt fuel bindings argTms st
            hb hargs argVs sArgs hresArgs
        cases hLocal : Concrete.Eval.tryLocalLookup g bindings with
        | none =>
          rw [hLocal] at heval
          exact applyGlobal_FnFree cd _hFOR _hRefClosed _hTermRefsDt fuel g argVs.toList
            sArgs (fun w hw => hargVs_FnFree w (Array.mem_toList_iff.mp hw)) v st' heval
        | some vCallee =>
          rw [hLocal] at heval
          -- vCallee is from bindings via `tryLocalLookup` (which uses bindings.find?).
          have hCallee : Value.FnFree vCallee := by
            unfold Concrete.Eval.tryLocalLookup at hLocal
            split at hLocal
            · -- .str .anonymous name branch
              rename_i nameStr _heq
              cases hfind : bindings.find? (·.1 == Local.str nameStr) with
              | none =>
                rw [hfind] at hLocal
                cases hLocal
              | some lv =>
                rw [hfind] at hLocal
                obtain ⟨l', vB⟩ := lv
                simp [Option.map] at hLocal
                subst hLocal
                have hmem := List.mem_of_find?_eq_some hfind
                exact hb _ hmem
            · cases hLocal
          exact applyLocal_FnFree cd _hFOR _hRefClosed _hTermRefsDt fuel vCallee
            argVs.toList sArgs hCallee
            (fun w hw => hargVs_FnFree w (Array.mem_toList_iff.mp hw)) v st' heval
  | add τ e a b =>
    rw [Concrete.Eval.interp_add] at heval
    cases htRefsDt with
    | add ha hb' =>
      apply evalBinField_FnFree cd _hFOR _hRefClosed _hTermRefsDt fuel bindings a b st _
        ?_ hb ha hb' v st' heval
      intro x y; exact .field _
  | sub τ e a b =>
    rw [Concrete.Eval.interp_sub] at heval
    cases htRefsDt with
    | sub ha hb' =>
      apply evalBinField_FnFree cd _hFOR _hRefClosed _hTermRefsDt fuel bindings a b st _
        ?_ hb ha hb' v st' heval
      intro x y; exact .field _
  | mul τ e a b =>
    rw [Concrete.Eval.interp_mul] at heval
    cases htRefsDt with
    | mul ha hb' =>
      apply evalBinField_FnFree cd _hFOR _hRefClosed _hTermRefsDt fuel bindings a b st _
        ?_ hb ha hb' v st' heval
      intro x y; exact .field _
  | eqZero τ e a =>
    rw [Concrete.Eval.interp_eqZero] at heval
    cases htRefsDt with
    | eqZero ha =>
      cases hres : Concrete.Eval.interp cd fuel bindings a st with
      | error err => rw [hres] at heval; cases heval
      | ok pair =>
        obtain ⟨va, sa⟩ := pair
        rw [hres] at heval
        cases va with
        | field g =>
          injection heval with hpair
          injection hpair with hv
          subst hv
          exact .field _
        | unit | tuple _ | array _ | ctor _ _ | fn _ | pointer _ _ => cases heval
  | proj τ e a n =>
    rw [Concrete.Eval.interp_proj] at heval
    cases htRefsDt with
    | proj ha =>
      cases hres : Concrete.Eval.interp cd fuel bindings a st with
      | error err => rw [hres] at heval; cases heval
      | ok pair =>
        obtain ⟨va, sa⟩ := pair
        rw [hres] at heval
        have hva_ff : Value.FnFree va :=
          interp_FnFree cd _hFOR _hRefClosed _hTermRefsDt fuel bindings a st
            hb ha va sa hres
        cases va with
        | tuple vs =>
          -- heval : (if h : n < vs.size then .ok (vs[n], sa) else .error _) = .ok (v, st')
          by_cases hidx : n < vs.size
          · simp [hidx] at heval
            have hv : vs[n]'hidx = v := heval.1
            subst hv
            cases hva_ff with
            | tuple h => exact h _ (Array.getElem_mem _)
          · simp [hidx] at heval
        | unit | field _ | array _ | ctor _ _ | fn _ | pointer _ _ => cases heval
  | get τ e a n =>
    rw [Concrete.Eval.interp_get] at heval
    cases htRefsDt with
    | get ha =>
      cases hres : Concrete.Eval.interp cd fuel bindings a st with
      | error err => rw [hres] at heval; cases heval
      | ok pair =>
        obtain ⟨va, sa⟩ := pair
        rw [hres] at heval
        have hva_ff : Value.FnFree va :=
          interp_FnFree cd _hFOR _hRefClosed _hTermRefsDt fuel bindings a st
            hb ha va sa hres
        cases va with
        | array vs =>
          by_cases hidx : n < vs.size
          · simp [hidx] at heval
            have hv : vs[n]'hidx = v := heval.1
            subst hv
            cases hva_ff with
            | array h => exact h _ (Array.getElem_mem _)
          · simp [hidx] at heval
        | unit | field _ | tuple _ | ctor _ _ | fn _ | pointer _ _ => cases heval
  | slice τ e a i j =>
    rw [Concrete.Eval.interp_slice] at heval
    cases htRefsDt with
    | slice ha =>
      cases hres : Concrete.Eval.interp cd fuel bindings a st with
      | error err => rw [hres] at heval; cases heval
      | ok pair =>
        obtain ⟨va, sa⟩ := pair
        rw [hres] at heval
        have hva_ff : Value.FnFree va :=
          interp_FnFree cd _hFOR _hRefClosed _hTermRefsDt fuel bindings a st
            hb ha va sa hres
        cases va with
        | array vs =>
          injection heval with hpair
          injection hpair with hv _
          subst hv
          cases hva_ff with
          | array h =>
            refine .array ?_
            intro w hw
            -- w ∈ (vs.extract i j) → ∃ k, w = vs[i+k] (within bounds).
            have hwmem : w ∈ vs := by
              rw [Array.mem_iff_getElem] at hw
              obtain ⟨k, hk, heqk⟩ := hw
              rw [Array.size_extract] at hk
              rw [Array.getElem_extract] at heqk
              rw [← heqk]
              exact Array.getElem_mem _
            exact h w hwmem
        | unit | field _ | tuple _ | ctor _ _ | fn _ | pointer _ _ => cases heval
  | set τ e a n vT =>
    -- IH on vT, then on a; .array (vs.set! n val) — set! preserves elementwise FnFree.
    rw [Concrete.Eval.interp_set] at heval
    cases htRefsDt with
    | set ha hv =>
      cases hresVT : Concrete.Eval.interp cd fuel bindings vT st with
      | error err => rw [hresVT] at heval; cases heval
      | ok pairVT =>
        obtain ⟨val, st1⟩ := pairVT
        rw [hresVT] at heval
        simp only at heval
        have hval_ff : Value.FnFree val :=
          interp_FnFree cd _hFOR _hRefClosed _hTermRefsDt fuel bindings vT st
            hb hv val st1 hresVT
        cases hresA : Concrete.Eval.interp cd fuel bindings a st1 with
        | error err => rw [hresA] at heval; cases heval
        | ok pairA =>
          obtain ⟨va, st2⟩ := pairA
          rw [hresA] at heval
          have hva_ff : Value.FnFree va :=
            interp_FnFree cd _hFOR _hRefClosed _hTermRefsDt fuel bindings a st1
              hb ha va st2 hresA
          cases va with
          | array vs =>
            by_cases hidx : n < vs.size
            · simp [hidx] at heval
              obtain ⟨hv', _⟩ := heval
              subst hv'
              cases hva_ff with
              | array hvs =>
                refine .array ?_
                intro w hw
                -- `set!` reduces to `setIfInBounds`. Membership is val (at n) or vs elt.
                simp only [Array.set!] at hw
                rw [Array.mem_iff_getElem] at hw
                obtain ⟨k, hk, heqk⟩ := hw
                have hsz : (vs.setIfInBounds n val).size = vs.size := by simp
                have hk' : k < vs.size := hsz ▸ hk
                by_cases hkn : k = n
                · -- At index n the element is val.
                  subst hkn
                  have hget : (vs.setIfInBounds k val)[k]'hk = val := by
                    simp [Array.getElem_setIfInBounds, hk']
                  rw [hget] at heqk
                  subst heqk; exact hval_ff
                · -- At index k ≠ n the element is vs[k].
                  have hkn' : ¬ n = k := fun h => hkn h.symm
                  have hget : (vs.setIfInBounds n val)[k]'hk = vs[k]'hk' := by
                    rw [Array.getElem_setIfInBounds]
                    rw [if_neg hkn']
                  rw [hget] at heqk
                  subst heqk
                  exact hvs _ (Array.getElem_mem _)
            · simp [hidx] at heval
          | unit | field _ | tuple _ | ctor _ _ | fn _ | pointer _ _ => cases heval
  | store τ e a =>
    -- LEAF (output): always .pointer w idx — FnFree.
    rw [Concrete.Eval.interp_store] at heval
    cases hres : Concrete.Eval.interp cd fuel bindings a st with
    | error err => rw [hres] at heval; cases heval
    | ok pair =>
      obtain ⟨va, sa⟩ := pair
      rw [hres] at heval
      injection heval with hpair
      injection hpair with hv
      subst hv
      exact .pointer _ _
  | load τ e a =>
    -- BLOCKED on SD-LoadType: same as `.letLoad`. The `.load` arm reads
    -- from `concreteTypToSource a.typ` which can contain `.function`. Without
    -- a `TypesNotFunction` invariant on the term-typed children, we can't
    -- conclude `unflattenValue` returns FnFree. See `.letLoad` BLOCKED note
    -- above for the closure path. Once SD-LoadType lands: closes via IH(a)
    -- → .pointer → storeLookup → unflattenValue → unflattenValue_FnFree.
    rw [Concrete.Eval.interp_load] at heval
    sorry
  | ptrVal τ e a =>
    -- IH(a) gives .pointer; output .field (.ofNat i) — FnFree.
    cases hres : Concrete.Eval.interp cd fuel bindings a st with
    | error err =>
      -- heval reduces via interp ptrVal; replace inner via hres.
      unfold Concrete.Eval.interp at heval
      rw [hres] at heval
      cases heval
    | ok pair =>
      obtain ⟨va, sa⟩ := pair
      unfold Concrete.Eval.interp at heval
      rw [hres] at heval
      cases va with
      | pointer w idx =>
        injection heval with hpair
        injection hpair with hv _
        subst hv
        exact .field _
      | unit | field _ | tuple _ | array _ | ctor _ _ | fn _ => cases heval
  | assertEq τ e a b r =>
    -- IH(a), IH(b), then IH(r)
    unfold Concrete.Eval.interp at heval
    split at heval
    · cases heval
    · rename_i v1 st1 _hres1
      split at heval
      · cases heval
      · rename_i v2 st2 _hres2
        split at heval
        · cases heval
        · cases htRefsDt with
          | assertEq ha hb' hr =>
            exact interp_FnFree cd _hFOR _hRefClosed _hTermRefsDt fuel bindings r
              st2 hb hr v st' heval
  | u8BitDecomposition τ e a =>
    rw [Concrete.Eval.interp_u8BitDecomposition] at heval
    cases hres : Concrete.Eval.interp cd fuel bindings a st with
    | error err => rw [hres] at heval; cases heval
    | ok pair =>
      obtain ⟨va, sa⟩ := pair
      rw [hres] at heval
      cases va with
      | field g =>
        injection heval with hpair
        injection hpair with hv
        subst hv
        exact FnFree_ofFn_field _ _
      | unit | tuple _ | array _ | ctor _ _ | fn _ | pointer _ _ => cases heval
  | u8ShiftLeft τ e a =>
    rw [Concrete.Eval.interp_u8ShiftLeft] at heval
    cases hres : Concrete.Eval.interp cd fuel bindings a st with
    | error err => rw [hres] at heval; cases heval
    | ok pair =>
      obtain ⟨va, sa⟩ := pair
      rw [hres] at heval
      cases va with
      | field g =>
        injection heval with hpair
        injection hpair with hv
        subst hv
        exact .field _
      | unit | tuple _ | array _ | ctor _ _ | fn _ | pointer _ _ => cases heval
  | u8ShiftRight τ e a =>
    rw [Concrete.Eval.interp_u8ShiftRight] at heval
    cases hres : Concrete.Eval.interp cd fuel bindings a st with
    | error err => rw [hres] at heval; cases heval
    | ok pair =>
      obtain ⟨va, sa⟩ := pair
      rw [hres] at heval
      cases va with
      | field g =>
        injection heval with hpair
        injection hpair with hv
        subst hv
        exact .field _
      | unit | tuple _ | array _ | ctor _ _ | fn _ | pointer _ _ => cases heval
  | u8Xor τ e a b =>
    rw [Concrete.Eval.interp_u8Xor] at heval
    cases htRefsDt with
    | u8Xor ha hb' =>
      apply evalBinField_FnFree cd _hFOR _hRefClosed _hTermRefsDt fuel bindings a b st _
        ?_ hb ha hb' v st' heval
      intro x y; exact .field _
  | u8Add τ e a b =>
    rw [Concrete.Eval.interp_u8Add] at heval
    cases htRefsDt with
    | u8Add ha hb' =>
      apply evalBinField_FnFree cd _hFOR _hRefClosed _hTermRefsDt fuel bindings a b st _
        ?_ hb ha hb' v st' heval
      intro x y; exact FnFree_two_field_tuple _ _
  | u8Sub τ e a b =>
    rw [Concrete.Eval.interp_u8Sub] at heval
    cases htRefsDt with
    | u8Sub ha hb' =>
      apply evalBinField_FnFree cd _hFOR _hRefClosed _hTermRefsDt fuel bindings a b st _
        ?_ hb ha hb' v st' heval
      intro x y; exact FnFree_two_field_tuple _ _
  | u8And τ e a b =>
    rw [Concrete.Eval.interp_u8And] at heval
    cases htRefsDt with
    | u8And ha hb' =>
      apply evalBinField_FnFree cd _hFOR _hRefClosed _hTermRefsDt fuel bindings a b st _
        ?_ hb ha hb' v st' heval
      intro x y; exact .field _
  | u8Or τ e a b =>
    rw [Concrete.Eval.interp_u8Or] at heval
    cases htRefsDt with
    | u8Or ha hb' =>
      apply evalBinField_FnFree cd _hFOR _hRefClosed _hTermRefsDt fuel bindings a b st _
        ?_ hb ha hb' v st' heval
      intro x y; exact .field _
  | u8LessThan τ e a b =>
    rw [Concrete.Eval.interp_u8LessThan] at heval
    cases htRefsDt with
    | u8LessThan ha hb' =>
      apply evalBinField_FnFree cd _hFOR _hRefClosed _hTermRefsDt fuel bindings a b st _
        ?_ hb ha hb' v st' heval
      intro x y; exact .field _
  | u32LessThan τ e a b =>
    rw [Concrete.Eval.interp_u32LessThan] at heval
    cases htRefsDt with
    | u32LessThan ha hb' =>
      apply evalBinField_FnFree cd _hFOR _hRefClosed _hTermRefsDt fuel bindings a b st _
        ?_ hb ha hb' v st' heval
      intro x y; exact .field _
  | debug τ e label tOpt r =>
    -- IH(r) — interp_debug is not in the inversion list; use raw unfold.
    unfold Concrete.Eval.interp at heval
    cases htRefsDt with
    | debug _hT hr =>
      exact interp_FnFree cd _hFOR _hRefClosed _hTermRefsDt fuel bindings r st
        hb hr v st' heval
  | ioGetInfo τ e k =>
    -- IH(k); output .tuple #[.field, .field] — FnFree_two_field_tuple.
    rw [Concrete.Eval.interp_ioGetInfo] at heval
    cases hres : Concrete.Eval.interp cd fuel bindings k st with
    | error err => rw [hres] at heval; cases heval
    | ok pair =>
      obtain ⟨vk, sk⟩ := pair
      rw [hres] at heval
      cases vk with
      | array vs =>
        cases hres' : Concrete.Eval.expectFieldArray vs with
        | none => simp [hres'] at heval
        | some keyGs =>
          simp [hres'] at heval
          cases hres'' : sk.ioBuffer.map[keyGs]? with
          | none => simp [hres''] at heval
          | some info =>
            simp [hres''] at heval
            obtain ⟨hv, _⟩ := heval
            subst hv
            exact FnFree_two_field_tuple _ _
      | unit | field _ | tuple _ | ctor _ _ | fn _ | pointer _ _ => cases heval
  | ioSetInfo τ e k iT lT r =>
    -- IH(k), IH(iT), IH(lT), IH(r). Eventually reaches IH(r).
    unfold Concrete.Eval.interp at heval
    -- Eval order is k -> iT -> lT, then match on result shapes, then IH(r).
    split at heval
    · cases heval
    · rename_i vk stk _hresk
      split at heval
      · cases heval
      · rename_i vi sti _hresi
        split at heval
        · cases heval
        · rename_i vl stl _hresl
          split at heval
          · -- happy path matching .array vs, .field iG, .field lG
            split at heval
            · cases heval  -- expectFieldArray = none
            · split at heval
              · cases heval  -- key already set
              · cases htRefsDt with
                | ioSetInfo _hk _hi _hl hr =>
                  exact interp_FnFree cd _hFOR _hRefClosed _hTermRefsDt fuel bindings r _
                    hb hr v st' heval
          all_goals cases heval
  | ioRead τ e idx n =>
    -- IH(idx); output .array (..|>.map .field).
    rw [Concrete.Eval.interp_ioRead] at heval
    cases hres : Concrete.Eval.interp cd fuel bindings idx st with
    | error err => rw [hres] at heval; cases heval
    | ok pair =>
      obtain ⟨vIdx, sidx⟩ := pair
      rw [hres] at heval
      cases vIdx with
      | field g =>
        by_cases hbnd : g.val.toNat + n > sidx.ioBuffer.data.size
        · simp [hbnd] at heval
        · simp [hbnd] at heval
          obtain ⟨hv, _⟩ := heval
          subst hv
          refine .array ?_
          intro w hw
          -- w ∈ (data.map .field).extract _ _ →
          -- ∃ k, w = (data.map .field)[i] = .field _.
          rw [Array.mem_iff_getElem] at hw
          obtain ⟨k, hk, heqk⟩ := hw
          have : w ∈ Array.map Value.field sidx.ioBuffer.data := by
            rw [Array.mem_iff_getElem]
            -- (extract data i j)[k] = data[i+k] (when in bounds).
            rw [Array.getElem_extract] at heqk
            refine ⟨g.val.toNat + k, ?_, heqk⟩
            rw [Array.size_extract] at hk
            rw [Array.size_map]
            omega
          rw [Array.mem_map] at this
          obtain ⟨g', _, heq⟩ := this
          subst heq
          exact .field _
      | unit | tuple _ | array _ | ctor _ _ | fn _ | pointer _ _ => cases heval
  | ioWrite τ e d r =>
    -- IH(d), IH(r).
    rw [Concrete.Eval.interp_ioWrite] at heval
    cases hres : Concrete.Eval.interp cd fuel bindings d st with
    | error err => rw [hres] at heval; cases heval
    | ok pair =>
      obtain ⟨vd, sd⟩ := pair
      rw [hres] at heval
      cases vd with
      | array vs =>
        cases hres' : Concrete.Eval.expectFieldArray vs with
        | none => simp [hres'] at heval
        | some dataGs =>
          simp [hres'] at heval
          cases htRefsDt with
          | ioWrite _hd hr =>
            exact interp_FnFree cd _hFOR _hRefClosed _hTermRefsDt fuel bindings r _
              hb hr v st' heval
      | unit | field _ | tuple _ | ctor _ _ | fn _ | pointer _ _ => cases heval
termination_by (fuel, 2, sizeOf t, 0)
decreasing_by all_goals first | decreasing_tactic | grind [sizeOf_toList_lt]

/-- Helper: bindings produced by `matchPattern` are FnFree whenever `scrut` is.
The bindings come from `(vars.zip vs).toList` (ref/tuple/array) or `[]`
(wildcard/field). The `.snd` projection of each pair is in `vs`, which is
FnFree-elementwise from `hscrut`. -/
private theorem matchPattern_bindingsFnFree {p : Concrete.Pattern} {scrut : Value}
    {bs : Bindings} (hscrut : Value.FnFree scrut)
    (h : Concrete.Eval.matchPattern p scrut = some bs) :
    BindingsFnFree bs := by
  -- Inline pointwise zip.snd-membership helper.
  have hzip_snd_mem :
      ∀ {α β} (xs : Array α) (ys : Array β) (p : α × β),
        p ∈ (xs.zip ys).toList → p.2 ∈ ys := by
    intro α β xs ys p hp
    rw [Array.toList_zip] at hp
    -- hp : p ∈ List.zip xs.toList ys.toList
    have : ∀ {α β} (xs : List α) (ys : List β) (p : α × β),
        p ∈ xs.zip ys → p.2 ∈ ys := by
      intro α β xs
      induction xs with
      | nil => intro ys p hp; simp [List.zip] at hp
      | cons x xs ih =>
        intro ys p hp
        cases ys with
        | nil => simp [List.zip] at hp
        | cons a as =>
          simp only [List.zip_cons_cons, List.mem_cons] at hp
          rcases hp with hp | hp
          · subst hp; exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ (ih as p hp)
    have hL := this _ _ _ hp
    exact Array.mem_toList_iff.mp hL
  cases p with
  | wildcard =>
    simp [Concrete.Eval.matchPattern] at h
    subst h
    intro x hx; cases hx
  | field g =>
    cases scrut with
    | field g' =>
      simp only [Concrete.Eval.matchPattern] at h
      split at h
      · injection h with h
        subst h
        intro x hx; cases hx
      · cases h
    | unit | tuple _ | array _ | ctor _ _ | fn _ | pointer _ _ => simp [Concrete.Eval.matchPattern] at h
  | ref g vars =>
    cases scrut with
    | ctor g' vs =>
      simp only [Concrete.Eval.matchPattern] at h
      split at h
      · cases h
      · split at h
        · cases h
        · injection h with h
          subst h
          intro p hp
          have hr := hzip_snd_mem vars vs p hp
          cases hscrut with
          | ctor _ hvs => exact hvs _ hr
    | unit | field _ | tuple _ | array _ | fn _ | pointer _ _ => simp [Concrete.Eval.matchPattern] at h
  | tuple vars =>
    cases scrut with
    | tuple vs =>
      simp only [Concrete.Eval.matchPattern] at h
      split at h
      · cases h
      · injection h with h
        subst h
        intro p hp
        have hr := hzip_snd_mem vars vs p hp
        cases hscrut with
        | tuple hvs => exact hvs _ hr
    | unit | field _ | ctor _ _ | array _ | fn _ | pointer _ _ => simp [Concrete.Eval.matchPattern] at h
  | array vars =>
    cases scrut with
    | array vs =>
      simp only [Concrete.Eval.matchPattern] at h
      split at h
      · cases h
      · injection h with h
        subst h
        intro p hp
        have hr := hzip_snd_mem vars vs p hp
        cases hscrut with
        | array hvs => exact hvs _ hr
    | unit | field _ | ctor _ _ | tuple _ | fn _ | pointer _ _ => simp [Concrete.Eval.matchPattern] at h

/-- Preservation through `evalMatchCases`. -/
theorem evalMatchCases_FnFree (cd : Concrete.Decls)
    (_hFOR : Concrete.Decls.FirstOrderReturn cd)
    (_hRefClosed : Concrete.Decls.RefClosed cd)
    (_hTermRefsDt : Concrete.Decls.TermRefsDt cd)
    (fuel : Nat) (bindings : Bindings) (st : EvalState) (scrut : Value)
    (cases : Array (Concrete.Pattern × Concrete.Term)) (defaultOpt : Option Concrete.Term)
    (i : Nat)
    (hb : BindingsFnFree bindings)
    (hscrut : Value.FnFree scrut)
    (hcasesRefs : ∀ pc ∈ cases, Concrete.Term.RefsDt cd pc.2)
    (hdefRefs : ∀ d, defaultOpt = some d → Concrete.Term.RefsDt cd d)
    (v : Value) (st' : EvalState)
    (heval : Concrete.Eval.evalMatchCases cd fuel bindings st scrut cases defaultOpt i
        = .ok (v, st')) :
    Value.FnFree v := by
  unfold Concrete.Eval.evalMatchCases at heval
  by_cases hi : i < cases.size
  · rw [dif_pos hi] at heval
    cases hmp : Concrete.Eval.matchPattern cases[i].fst scrut with
    | none =>
      rw [hmp] at heval
      simp at heval
      -- recursive call on i+1
      exact evalMatchCases_FnFree cd _hFOR _hRefClosed _hTermRefsDt fuel bindings st
        scrut cases defaultOpt (i + 1) hb hscrut hcasesRefs hdefRefs v st' heval
    | some bs =>
      rw [hmp] at heval
      simp at heval
      -- happy path: interp on cases[i].snd with bs ++ bindings
      have hbs_FnFree : BindingsFnFree bs := matchPattern_bindingsFnFree hscrut hmp
      have hb_ext : BindingsFnFree (bs ++ bindings) := BindingsFnFree.append hbs_FnFree hb
      have hcase_refs : Concrete.Term.RefsDt cd cases[i].snd :=
        hcasesRefs _ (Array.getElem_mem hi)
      exact interp_FnFree cd _hFOR _hRefClosed _hTermRefsDt fuel (bs ++ bindings)
        cases[i].snd st hb_ext hcase_refs v st' heval
  · rw [dif_neg hi] at heval
    cases hd : defaultOpt with
    | none => rw [hd] at heval; cases heval
    | some body =>
      rw [hd] at heval
      have hbody_refs : Concrete.Term.RefsDt cd body := hdefRefs body hd
      exact interp_FnFree cd _hFOR _hRefClosed _hTermRefsDt fuel bindings body st
        hb hbody_refs v st' heval
termination_by (fuel, 2, sizeOf cases + sizeOf defaultOpt, cases.size - i)
decreasing_by
  all_goals first
    | decreasing_tactic
    | (apply Prod.Lex.right; apply Prod.Lex.right; apply Prod.Lex.left
       have h := Array.sizeOf_get cases i ‹_›
       have hpair : sizeOf cases[i].snd ≤ sizeOf cases[i] := by
         rcases hcp : cases[i] with ⟨a, b⟩
         show sizeOf b ≤ sizeOf (a, b)
         simp [Prod.mk.sizeOf_spec]
       omega)
    | (apply Prod.Lex.right; apply Prod.Lex.right; apply Prod.Lex.right
       omega)

/-- Preservation through `evalList`. -/
theorem evalList_FnFree (cd : Concrete.Decls)
    (_hFOR : Concrete.Decls.FirstOrderReturn cd)
    (_hRefClosed : Concrete.Decls.RefClosed cd)
    (_hTermRefsDt : Concrete.Decls.TermRefsDt cd)
    (fuel : Nat) (bindings : Bindings) (ts : List Concrete.Term) (st : EvalState)
    (hb : BindingsFnFree bindings)
    (htsRefs : ∀ t ∈ ts, Concrete.Term.RefsDt cd t)
    (vs : Array Value) (st' : EvalState)
    (heval : Concrete.Eval.evalList cd fuel bindings ts st = .ok (vs, st')) :
    ∀ v ∈ vs, Value.FnFree v :=
  match ts, heval with
  | [], heval => by
    unfold Concrete.Eval.evalList at heval
    injection heval with hpair
    injection hpair with hvs _hst
    subst hvs
    intro v hv
    simp at hv
  | (t :: tsTail), heval => by
    unfold Concrete.Eval.evalList at heval
    split at heval
    · cases heval  -- error
    · rename_i v0 st0 hres
      split at heval
      · cases heval  -- error in tail
      · rename_i vsTail stTail hresTail
        injection heval with hpair
        injection hpair with hvs hst
        subst hvs hst
        -- v0 is FnFree by interp_FnFree IH on t.
        have ht_refs : Concrete.Term.RefsDt cd t := htsRefs _ (List.mem_cons_self)
        have hv0 : Value.FnFree v0 :=
          interp_FnFree cd _hFOR _hRefClosed _hTermRefsDt fuel bindings t st
            hb ht_refs v0 st0 hres
        have hts_refs : ∀ t' ∈ tsTail, Concrete.Term.RefsDt cd t' := by
          intro t' ht'mem
          exact htsRefs _ (List.mem_cons_of_mem _ ht'mem)
        have hihTail :=
          evalList_FnFree cd _hFOR _hRefClosed _hTermRefsDt fuel bindings tsTail st0
            hb hts_refs vsTail stTail hresTail
        intro v hv
        rw [Array.mem_iff_getElem] at hv
        obtain ⟨i, hi, heq⟩ := hv
        rw [Array.size_append] at hi
        have hsize_one : (#[v0] : Array Value).size = 1 := by simp
        by_cases hi0 : i = 0
        · subst hi0
          have hzero : (#[v0] ++ vsTail)[0] = v0 := by
            simp [Array.getElem_append]
          rw [hzero] at heq
          subst heq; exact hv0
        · have hi' : i - 1 < vsTail.size := by omega
          have hmem : v ∈ vsTail := by
            rw [← heq]
            rw [Array.getElem_append]
            split
            · rename_i hcase
              rw [hsize_one] at hcase; omega
            · exact Array.getElem_mem _
          exact hihTail v hmem
termination_by (fuel, 2, sizeOf ts, 0)
decreasing_by
  all_goals first
    | decreasing_tactic
    | (apply Prod.Lex.right; apply Prod.Lex.right; apply Prod.Lex.left
       simp only [List.cons.sizeOf_spec]; omega)

/-- Preservation through `evalBinField`. The closure `k` here always returns
either `.field _` or `.tuple #[.field _, .field _]`, both FnFree. -/
theorem evalBinField_FnFree (cd : Concrete.Decls)
    (_hFOR : Concrete.Decls.FirstOrderReturn cd)
    (_hRefClosed : Concrete.Decls.RefClosed cd)
    (_hTermRefsDt : Concrete.Decls.TermRefsDt cd)
    (fuel : Nat) (bindings : Bindings) (t1 t2 : Concrete.Term) (st : EvalState)
    (k : G → G → Value)
    (hk : ∀ a b, Value.FnFree (k a b))
    (hb : BindingsFnFree bindings)
    (ht1Refs : Concrete.Term.RefsDt cd t1) (ht2Refs : Concrete.Term.RefsDt cd t2)
    (v : Value) (st' : EvalState)
    (heval : Concrete.Eval.evalBinField cd fuel bindings t1 t2 st k = .ok (v, st')) :
    Value.FnFree v := by
  unfold Concrete.Eval.evalBinField at heval
  split at heval
  · cases heval  -- error
  · rename_i v1_st1 hres1
    obtain ⟨v1, st1⟩ := v1_st1
    split at heval
    · cases heval  -- error
    · rename_i v2_st2 hres2
      obtain ⟨v2, st2⟩ := v2_st2
      -- match on v1, v2 — closure k returns its result only when both are .field.
      split at heval
      · -- both .field
        rename_i a b
        injection heval with hpair
        injection hpair with hv
        subst hv
        exact hk a b
      · cases heval  -- type mismatch
termination_by (fuel, 2, sizeOf t1 + sizeOf t2 + 1, 0)

end

/-! #### Main body — closes via `applyGlobal_FnFree`. -/

/-- Main result. Sig matches `Concrete.Eval.runFunction_preserves_FnFree`
(post-TermRefsDt absorption). Reduces to `applyGlobal_FnFree` from the
mutual block above. -/
theorem runFunction_preserves_FnFree_body
    (cd : Concrete.Decls)
    (name : Global) (args : List Value) (io₀ : IOBuffer) (fuel : Nat)
    (_hFOR : Concrete.Decls.FirstOrderReturn cd)
    (_hRefClosed : Concrete.Decls.RefClosed cd)
    (_hTermRefsDt : Concrete.Decls.TermRefsDt cd)
    (_hargsFnFree : ∀ v ∈ args, Value.FnFree v)
    (v : Value) (io : IOBuffer)
    (_hrun : Concrete.Eval.runFunction cd name args io₀ fuel = .ok (v, io)) :
    Value.FnFree v := by
  -- Unfold runFunction: it's a let-binding + outer match. Reduce by hand.
  have hrun_eq :
      Concrete.Eval.runFunction cd name args io₀ fuel =
      (match Concrete.Eval.applyGlobal cd fuel name args { ioBuffer := io₀ } with
       | .error e => Except.error e
       | .ok (v, st') => .ok (v, st'.ioBuffer)) := rfl
  rw [hrun_eq] at _hrun
  split at _hrun
  · cases _hrun
  · rename_i v' st' hcall
    injection _hrun with hpair
    injection hpair with hv _
    subst hv
    exact applyGlobal_FnFree cd _hFOR _hRefClosed _hTermRefsDt fuel name args
      { ioBuffer := io₀ } _hargsFnFree v' st' hcall

end FnFreeBody

/-- Concrete-eval preserves `FnFree` on returns when args are FnFree, the
decls have first-order inputs/outputs (ruling out `.fn`-valued returns via
`.ref g` where `g` is a function key), and the decls' function bodies are
well-typed. Type-soundness consequence: well-typed first-order program returns
first-order values. BLOCKED ON: type-preservation theorem through
`Concrete.Eval.runFunction` — needs an inductive over fuel + recursion through
callees. -/
theorem Concrete.Eval.runFunction_preserves_FnFree
    (cd : Concrete.Decls)
    (name : Global) (args : List Value) (io₀ : IOBuffer) (fuel : Nat)
    (_hFOR : Concrete.Decls.FirstOrderReturn cd)
    -- Sig strengthened (2026-04-24, SORRY_AUDIT_AGENT1.md §1): `.ref g` in
    -- concrete types must resolve to a `.dataType` (not `.function`), else
    -- `.ref fSelf` with `f.output = .ref fSelf` satisfies `FirstOrderReturn`
    -- yet evaluates to `.fn fSelf` — counterexample to FALSE-as-stated.
    (_hRefClosed : Concrete.Decls.RefClosed cd)
    -- Sig strengthened (2026-04-24, `FnFreeSigFixScratch`): TYPE-level
    -- `RefClosed` insufficient because `Concrete.Term.ref g` TERM evaluates
    -- to `.fn g` when `g` names a function. `TermRefsDt` rules that out.
    (_hTermRefsDt : Concrete.Decls.TermRefsDt cd)
    (_hargsFnFree : ∀ v ∈ args, Value.FnFree v)
    (v : Value) (io : IOBuffer)
    (_hrun : Concrete.Eval.runFunction cd name args io₀ fuel = .ok (v, io)) :
    Value.FnFree v :=
  FnFreeBody.runFunction_preserves_FnFree_body
    cd name args io₀ fuel _hFOR _hRefClosed _hTermRefsDt _hargsFnFree v io _hrun

/-! ### `FirstOrderReturn` bridge — typedDecls → concrete decls.

Composes the structural preservation lemmas (`rewriteTyp`, `typToConcrete`)
through concretize's pipeline (drain + `concretizeBuild` + `step4Lower` fold)
to lift `Typed.Decls.FirstOrderReturn` to `Concrete.Decls.FirstOrderReturn`.

Source-side is handled by `WellFormed.FirstOrderReturn` directly (parallel to
`DirectDatatypeDAGAcyclic`): the user-facing obligation quantifies over the
post-`checkAndSimplify` typedDecls, so the bridge at
`CompilerCorrect.compile_correct` collapses to a single hypothesis
application into `concretize_preserves_FirstOrderReturn`. -/

/-- The empty substitution trivially maps no globals. Used to discharge
`rewriteTyp_preserves_FirstOrder`'s `_hsubstFO` hypothesis at `emptySubst`. -/
theorem emptySubst_FO : ∀ (g : Global) (t' : Typ),
    (fun (_ : Global) => (none : Option Typ)) g = some t' → Typ.FirstOrder t' := by
  intro g t' hget; cases hget

/-! ### Helpers for `FirstOrder` preservation lemmas below. -/

/-- Membership in `(arr.attach.map f)` exposes the preimage directly. -/
private theorem mem_of_attach_map {α β : Type _}
    (arr : Array α) (f : {x // x ∈ arr} → β) {b : β}
    (h : b ∈ arr.attach.map f) :
    ∃ (a : α) (ha : a ∈ arr), f ⟨a, ha⟩ = b := by
  rw [Array.mem_iff_getElem] at h
  obtain ⟨i, hi, heq⟩ := h
  have hi' : i < arr.attach.size := by
    rw [Array.size_map] at hi; exact hi
  have hi'' : i < arr.size := by
    rw [Array.size_attach] at hi'; exact hi'
  refine ⟨arr[i]'hi'', Array.getElem_mem hi'', ?_⟩
  rw [← heq]
  rw [Array.getElem_map]
  congr 1
  apply Subtype.eq
  simp [Array.getElem_attach]

/-- Pointwise FO-propagation through `List.mapM`. -/
private theorem List.mem_mapM_ok_forall {α β ε : Type}
    {f : α → Except ε β} {P : α → Prop} {Q : β → Prop}
    (hstep : ∀ x, P x → ∀ fx, f x = .ok fx → Q fx) :
    ∀ (l : List α) (ls : List β),
      (∀ x ∈ l, P x) →
      l.mapM f = .ok ls →
      ∀ y ∈ ls, Q y
  | [], ls, _, h, y, hy => by
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h
    cases hy
  | (x :: xs), ls, hP, h, y, hy => by
    simp only [List.mapM_cons, bind, Except.bind] at h
    split at h
    · cases h
    rename_i fx hfx
    split at h
    · cases h
    rename_i fxs hfxs
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    cases hy with
    | head _ =>
      exact hstep x (hP x (List.Mem.head _)) y hfx
    | tail _ hy' =>
      exact List.mem_mapM_ok_forall hstep xs fxs
        (fun z hz => hP z (List.Mem.tail _ hz)) hfxs y hy'

/-- Array-level counterpart. -/
private theorem Array.mem_mapM_ok_forall {α β ε : Type}
    {f : α → Except ε β} {P : α → Prop} {Q : β → Prop}
    (hstep : ∀ x, P x → ∀ fx, f x = .ok fx → Q fx)
    (a : Array α) (bs : Array β)
    (hP : ∀ x ∈ a, P x)
    (h : a.mapM f = .ok bs) :
    ∀ y ∈ bs, Q y := by
  intro y hy
  have h' : a.toList.mapM f = .ok bs.toList := by
    rw [Array.mapM_eq_mapM_toList] at h
    cases hres : a.toList.mapM f with
    | error e =>
      rw [hres] at h
      cases h
    | ok ls =>
      rw [hres] at h
      simp only [Functor.map, Except.map, Except.ok.injEq] at h
      have hbs : bs.toList = ls := by rw [← h]
      rw [hbs]
  have hPl : ∀ x ∈ a.toList, P x :=
    fun x hx => hP x (Array.mem_toList_iff.mp hx)
  have hylist : y ∈ bs.toList := Array.mem_toList_iff.mpr hy
  exact List.mem_mapM_ok_forall hstep a.toList bs.toList hPl h' y hylist

/-- `rewriteTyp` preserves `Typ.FirstOrder`. Structural induction on the
`Typ.FirstOrder` predicate. -/
theorem rewriteTyp_preserves_FirstOrder
    (subst : Global → Option Typ) (mono : MonoMap) {t : Typ}
    (hsubstFO : ∀ g t', subst g = some t' → Typ.FirstOrder t')
    (hFO : Typ.FirstOrder t) :
    Typ.FirstOrder (rewriteTyp subst mono t) := by
  induction hFO with
  | unit => unfold rewriteTyp; exact .unit
  | field => unfold rewriteTyp; exact .field
  | mvar n => unfold rewriteTyp; exact .mvar n
  | ref g =>
    unfold rewriteTyp
    cases hsub : subst g with
    | none => simp only [hsub, Option.getD_none]; exact .ref g
    | some t' =>
      simp only [hsub, Option.getD_some]
      exact hsubstFO g t' hsub
  | @tuple ts _ ih =>
    unfold rewriteTyp
    refine .tuple ?_
    intro t' ht'
    obtain ⟨t0, ht0mem, ht0eq⟩ := mem_of_attach_map ts _ ht'
    subst ht0eq
    exact ih t0 ht0mem
  | @array t n _ iht =>
    unfold rewriteTyp
    exact .array iht
  | @pointer t _ iht =>
    unfold rewriteTyp
    exact .pointer iht
  | @app g args _ ih =>
    unfold rewriteTyp
    cases hm : mono[(g, args)]? with
    | some concName =>
      simp only [hm]
      exact .ref concName
    | none =>
      simp only [hm]
      refine .app ?_
      intro t' ht'
      obtain ⟨t0, ht0mem, ht0eq⟩ := mem_of_attach_map args _ ht'
      subst ht0eq
      exact ih t0 ht0mem

/-- `typToConcrete` lifts `Typ.FirstOrder` to `Concrete.Typ.FirstOrder`.
Structural induction on `Typ.FirstOrder`; `.mvar` arm errors (contradicts
`hrun`). -/
theorem typToConcrete_preserves_FirstOrder
    {mono : Std.HashMap (Global × Array Typ) Global} {t : Typ} {t' : Concrete.Typ}
    (hFO : Typ.FirstOrder t)
    (hrun : typToConcrete mono t = .ok t') :
    Concrete.Typ.FirstOrder t' := by
  induction hFO generalizing t' with
  | unit =>
    unfold typToConcrete at hrun
    simp only [pure, Except.pure, Except.ok.injEq] at hrun
    subst hrun
    exact .unit
  | field =>
    unfold typToConcrete at hrun
    simp only [pure, Except.pure, Except.ok.injEq] at hrun
    subst hrun
    exact .field
  | mvar n =>
    unfold typToConcrete at hrun
    cases hrun
  | ref g =>
    unfold typToConcrete at hrun
    simp only [pure, Except.pure, Except.ok.injEq] at hrun
    subst hrun
    exact .ref g
  | @tuple ts htsFO ih =>
    unfold typToConcrete at hrun
    simp only [bind, Except.bind, pure, Except.pure] at hrun
    split at hrun
    · cases hrun
    rename_i ls hls
    simp only [Except.ok.injEq] at hrun
    subst hrun
    refine .tuple ?_
    intro t0 ht0mem
    have hls' : ts.mapM (typToConcrete mono) = .ok ls := by
      rw [Array.mapM_subtype (g := fun t => typToConcrete mono t) (fun _ _ => rfl)] at hls
      rw [Array.unattach_attach] at hls
      exact hls
    refine Array.mem_mapM_ok_forall
      (P := fun x => x ∈ ts)
      (Q := Concrete.Typ.FirstOrder)
      ?_ ts ls (fun x hx => hx) hls' t0 ht0mem
    intro x hxMem fx hfx
    exact ih x hxMem hfx
  | @array t n _ iht =>
    unfold typToConcrete at hrun
    simp only [bind, Except.bind, pure, Except.pure] at hrun
    split at hrun
    · cases hrun
    rename_i ct hct
    simp only [Except.ok.injEq] at hrun
    subst hrun
    exact .array (iht hct)
  | @pointer t _ iht =>
    unfold typToConcrete at hrun
    simp only [bind, Except.bind, pure, Except.pure] at hrun
    split at hrun
    · cases hrun
    rename_i ct hct
    simp only [Except.ok.injEq] at hrun
    subst hrun
    exact .pointer (iht hct)
  | @app g args _ _ =>
    unfold typToConcrete at hrun
    simp only [bind, Except.bind, pure, Except.pure] at hrun
    split at hrun
    · rename_i concName _
      simp only [Except.ok.injEq] at hrun
      subst hrun
      exact .ref concName
    · rename_i _
      simp only [Except.ok.injEq] at hrun
      subst hrun
      exact .ref g

/-! ### `concretizeBuild` FO-on-outputs invariant. -/

/-- FO-on-function-outputs invariant for partial builds. -/
private def FOInv (acc : Typed.Decls) : Prop :=
  ∀ g f, acc.getByKey g = some (.function f) → Typ.FirstOrder f.output

private theorem FOInv_default : FOInv (default : Typed.Decls) := by
  intro g f hget
  exfalso
  have : (default : Typed.Decls).getByKey g = none := by
    unfold IndexMap.getByKey
    show ((default : Typed.Decls).indices[g]?).bind _ = none
    have : (default : Typed.Decls).indices[g]? = none := by
      show ((default : Std.HashMap Global Nat))[g]? = none
      exact Std.HashMap.getElem?_empty
    rw [this]; rfl
  rw [this] at hget; cases hget

private theorem fromSource_preserves_FOInv
    (typedDecls : Typed.Decls) (mono : MonoMap)
    (htdFO : Typed.Decls.FirstOrderReturn typedDecls) :
    FOInv
      (typedDecls.pairs.foldl
        (fun acc p =>
          let (key, d) := p
          match d with
          | .function f =>
            if f.params.isEmpty then
              let newInputs := f.inputs.map fun (l, t) => (l, rewriteTyp (fun _ => none) mono t)
              let newOutput := rewriteTyp (fun _ => none) mono f.output
              let newBody := rewriteTypedTerm typedDecls (fun _ => none) mono f.body
              acc.insert key (.function
                { f with inputs := newInputs, output := newOutput, body := newBody })
            else acc
          | .dataType dt =>
            if dt.params.isEmpty then
              let newCtors := dt.constructors.map fun c =>
                { c with argTypes := c.argTypes.map (rewriteTyp (fun _ => none) mono) }
              acc.insert key (.dataType { dt with constructors := newCtors })
            else acc
          | .constructor dt c =>
            if dt.params.isEmpty then
              let newArgTypes := c.argTypes.map (rewriteTyp (fun _ => none) mono)
              let newCtor : Constructor := { c with argTypes := newArgTypes }
              let rewrittenCtors := dt.constructors.map fun c' =>
                { c' with argTypes := c'.argTypes.map (rewriteTyp (fun _ => none) mono) }
              let newDt : DataType := { dt with constructors := rewrittenCtors }
              acc.insert key (.constructor newDt newCtor)
            else acc)
        default) := by
  refine Array.foldl_induction
    (motive := fun _ acc => FOInv acc) FOInv_default ?_
  intro i acc hinv
  intro g f hget
  generalize hpr : typedDecls.pairs[i.val] = pr at hget
  have hprmem : pr ∈ typedDecls.pairs := by
    rw [← hpr]; exact Array.getElem_mem i.isLt
  obtain ⟨key, d⟩ := pr
  cases d with
  | function tf =>
    by_cases hparams : tf.params.isEmpty
    · simp only [hparams, if_true] at hget
      by_cases hkey : (key == g) = true
      · have hkeyEq : key = g := LawfulBEq.eq_of_beq hkey
        subst hkeyEq
        rw [IndexMap.getByKey_insert_self] at hget
        simp only [Option.some.injEq, Typed.Declaration.function.injEq] at hget
        rw [← hget]
        apply rewriteTyp_preserves_FirstOrder (fun _ => none) mono
          emptySubst_FO
        exact htdFO key tf (IndexMap.getByKey_of_mem_pairs _ _ _
          (Array.mem_toList_iff.mpr hprmem))
      · have hne : (key == g) = false := Bool.not_eq_true _ |>.mp hkey
        rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
        exact hinv g f hget
    · simp only [hparams, if_false] at hget
      exact hinv g f hget
  | dataType dt =>
    by_cases hparams : dt.params.isEmpty
    · simp only [hparams, if_true] at hget
      by_cases hkey : (key == g) = true
      · have hkeyEq : key = g := LawfulBEq.eq_of_beq hkey
        subst hkeyEq
        rw [IndexMap.getByKey_insert_self] at hget
        cases hget
      · have hne : (key == g) = false := Bool.not_eq_true _ |>.mp hkey
        rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
        exact hinv g f hget
    · simp only [hparams, if_false] at hget
      exact hinv g f hget
  | constructor dt c =>
    by_cases hparams : dt.params.isEmpty
    · simp only [hparams, if_true] at hget
      by_cases hkey : (key == g) = true
      · have hkeyEq : key = g := LawfulBEq.eq_of_beq hkey
        subst hkeyEq
        rw [IndexMap.getByKey_insert_self] at hget
        cases hget
      · have hne : (key == g) = false := Bool.not_eq_true _ |>.mp hkey
        rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
        exact hinv g f hget
    · simp only [hparams, if_false] at hget
      exact hinv g f hget

private theorem withNewDts_preserves_FOInv
    (mono : MonoMap) (newDataTypes : Array DataType) (init : Typed.Decls)
    (hinit : FOInv init) :
    FOInv
      (newDataTypes.foldl
        (fun acc dt =>
          let rewrittenCtors := dt.constructors.map fun c =>
            { c with argTypes := c.argTypes.map (rewriteTyp (fun _ => none) mono) }
          let newDt : DataType := { dt with constructors := rewrittenCtors }
          let acc' := acc.insert dt.name (.dataType newDt)
          rewrittenCtors.foldl
            (fun acc'' c =>
              let cName := dt.name.pushNamespace c.nameHead
              acc''.insert cName (.constructor newDt c))
            acc')
        init) := by
  refine Array.foldl_induction (motive := fun _ acc => FOInv acc) hinit ?_
  intro i acc hacc
  generalize hdt : newDataTypes[i.val] = dt
  let newDt : DataType := { dt with
    constructors := dt.constructors.map fun c =>
      { c with argTypes := c.argTypes.map (rewriteTyp (fun _ => none) mono) } }
  have hAccInsDt : FOInv (acc.insert dt.name (.dataType newDt)) := by
    intro k tf hget
    by_cases hkey : (dt.name == k) = true
    · have hkeyEq : dt.name = k := LawfulBEq.eq_of_beq hkey
      subst hkeyEq
      rw [IndexMap.getByKey_insert_self] at hget
      cases hget
    · have hne : (dt.name == k) = false := Bool.not_eq_true _ |>.mp hkey
      rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
      exact hacc k tf hget
  have hInner :
      ∀ (cs : List Constructor) (accInit : Typed.Decls),
        FOInv accInit →
        FOInv (cs.foldl
          (fun acc'' c =>
            let cName := dt.name.pushNamespace c.nameHead
            acc''.insert cName (.constructor newDt c))
          accInit) := by
    intro cs
    induction cs with
    | nil => intro accInit hAccInit; exact hAccInit
    | cons c rest ih =>
      intro accInit hAccInit
      apply ih
      intro k tf hget
      by_cases hkey : (dt.name.pushNamespace c.nameHead == k) = true
      · have hkeyEq : dt.name.pushNamespace c.nameHead = k := LawfulBEq.eq_of_beq hkey
        subst hkeyEq
        rw [IndexMap.getByKey_insert_self] at hget
        cases hget
      · have hne : (dt.name.pushNamespace c.nameHead == k) = false :=
          Bool.not_eq_true _ |>.mp hkey
        rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
        exact hAccInit k tf hget
  exact hInner _ _ hAccInsDt

private theorem newFunctions_preserves_FOInv
    (typedDecls : Typed.Decls) (mono : MonoMap)
    (newFunctions : Array Typed.Function) (init : Typed.Decls)
    (hinit : FOInv init)
    (hnfFO : ∀ f ∈ newFunctions, Typ.FirstOrder f.output) :
    FOInv
      (newFunctions.foldl
        (fun acc f =>
          let newInputs := f.inputs.map fun (l, t) => (l, rewriteTyp (fun _ => none) mono t)
          let newOutput := rewriteTyp (fun _ => none) mono f.output
          let newBody := rewriteTypedTerm typedDecls (fun _ => none) mono f.body
          let newF : Typed.Function :=
            { f with inputs := newInputs, output := newOutput, body := newBody }
          acc.insert f.name (.function newF))
        init) := by
  refine Array.foldl_induction (motive := fun _ acc => FOInv acc) hinit ?_
  intro i acc hacc
  intro g f hget
  generalize htf : newFunctions[i.val] = tf at hget
  have htfmem : tf ∈ newFunctions := by
    rw [← htf]; exact Array.getElem_mem i.isLt
  by_cases hkey : (tf.name == g) = true
  · have hkeyEq : tf.name = g := LawfulBEq.eq_of_beq hkey
    subst hkeyEq
    rw [IndexMap.getByKey_insert_self] at hget
    simp only [Option.some.injEq, Typed.Declaration.function.injEq] at hget
    rw [← hget]
    apply rewriteTyp_preserves_FirstOrder (fun _ => none) mono emptySubst_FO
    exact hnfFO tf htfmem
  · have hne : (tf.name == g) = false := Bool.not_eq_true _ |>.mp hkey
    rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
    exact hacc g f hget

/-- `concretizeBuild` preserves FO on every function output.
Requires: FO on every function in `typedDecls` (hypothesis) and FO on every
function in `newFunctions` (drain invariant). -/
theorem concretizeBuild_preserves_FirstOrderReturn
    {typedDecls : Typed.Decls} {mono : MonoMap}
    {newFunctions : Array Typed.Function} {newDataTypes : Array DataType}
    (htdFO : Typed.Decls.FirstOrderReturn typedDecls)
    (hnfFO : ∀ f ∈ newFunctions, Typ.FirstOrder f.output) :
    ∀ g f, (concretizeBuild typedDecls mono newFunctions newDataTypes).getByKey g
            = some (.function f) → Typ.FirstOrder f.output := by
  unfold concretizeBuild
  have h1 := fromSource_preserves_FOInv typedDecls mono htdFO
  have h2 := withNewDts_preserves_FOInv mono newDataTypes _ h1
  exact newFunctions_preserves_FOInv typedDecls mono newFunctions _ h2 hnfFO

/-- `step4Lower` applied to a function entry yields a concrete function with
`output := typToConcrete emptyMono f.output`. FO lifts via
`typToConcrete_preserves_FirstOrder`. -/
theorem step4Lower_function_preserves_FirstOrder
    {acc : Concrete.Decls} {name : Global} {f : Typed.Function}
    {r : Concrete.Decls}
    (hrun : step4Lower acc (name, .function f) = .ok r)
    (hfFO : Typ.FirstOrder f.output) :
    ∃ cf, r.getByKey name = some (.function cf) ∧ Concrete.Typ.FirstOrder cf.output := by
  unfold step4Lower at hrun
  simp only [bind, Except.bind, pure, Except.pure] at hrun
  split at hrun
  · rename_i err _ ; cases hrun
  rename_i _cInputs _hInputs
  split at hrun
  · rename_i err _ ; cases hrun
  rename_i cOutput hOutput
  split at hrun
  · rename_i err _ ; cases hrun
  rename_i _cBody _hBody
  simp only [Except.ok.injEq] at hrun
  subst hrun
  let cf : Concrete.Function :=
    { name := f.name, inputs := _cInputs, output := cOutput,
      body := _cBody, entry := f.entry }
  refine ⟨cf, ?_, ?_⟩
  · rw [IndexMap.getByKey_insert_self]
  · exact typToConcrete_preserves_FirstOrder hfFO hOutput

/-- `step4Lower` fold preserves the FO-on-outputs invariant.

Invariant:
`P acc := ∀ g cf, acc.getByKey g = some (.function cf) → Concrete.Typ.FirstOrder cf.output`.

Per-step:
- function arm dispatches to `step4Lower_function_preserves_FirstOrder`.
- dataType / constructor arms insert non-function entries; the self-case
  cannot hit `.function cf`, the other-case appeals to the prior
  invariant via `IndexMap.getByKey_insert_of_beq_false`. -/
theorem step4Lower_fold_preserves_FirstOrderReturn
    {monoDecls : Typed.Decls} {concDecls : Concrete.Decls}
    (hmdFO : ∀ g f, monoDecls.getByKey g = some (.function f) → Typ.FirstOrder f.output)
    (hfold : monoDecls.foldlM (init := default) step4Lower = .ok concDecls) :
    ∀ g f, concDecls.getByKey g = some (.function f) →
           Concrete.Typ.FirstOrder f.output := by
  rw [IndexMap.indexMap_foldlM_eq_list_foldlM] at hfold
  let P : Concrete.Decls → Prop := fun acc =>
    ∀ g cf, acc.getByKey g = some (.function cf) → Concrete.Typ.FirstOrder cf.output
  have hPdefault : P (default : Concrete.Decls) := by
    intro g cf hget
    exfalso
    have hne : (default : Concrete.Decls).getByKey g = none := by
      unfold IndexMap.getByKey
      show ((default : Concrete.Decls).indices[g]?).bind _ = none
      have : (default : Concrete.Decls).indices[g]? = none := by
        show ((default : Std.HashMap Global Nat))[g]? = none
        exact Std.HashMap.getElem?_empty
      rw [this]; rfl
    rw [hne] at hget; cases hget
  apply List.foldlM_except_invariant monoDecls.pairs.toList _ _ _ _ hfold
  · exact hPdefault
  intro acc ⟨name, d⟩ acc' hxmem hstep hPacc
  cases d with
  | function f =>
    have hfFO : Typ.FirstOrder f.output := by
      apply hmdFO name f
      exact IndexMap.getByKey_of_mem_pairs _ _ _ hxmem
    obtain ⟨cf, hcf_get, hcf_fo⟩ := step4Lower_function_preserves_FirstOrder hstep hfFO
    intro k tf hget
    by_cases hkn : (name == k) = true
    · have hkEq : name = k := LawfulBEq.eq_of_beq hkn
      subst hkEq
      rw [hcf_get] at hget
      simp only [Option.some.injEq, Concrete.Declaration.function.injEq] at hget
      rw [← hget]; exact hcf_fo
    · have hne : (name == k) = false := Bool.not_eq_true _ |>.mp hkn
      unfold step4Lower at hstep
      simp only [bind, Except.bind, pure, Except.pure] at hstep
      split at hstep
      · rename_i err _ ; cases hstep
      split at hstep
      · rename_i err _ ; cases hstep
      split at hstep
      · rename_i err _ ; cases hstep
      simp only [Except.ok.injEq] at hstep
      subst hstep
      rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
      exact hPacc k tf hget
  | dataType dt =>
    unfold step4Lower at hstep
    simp only [bind, Except.bind, pure, Except.pure] at hstep
    split at hstep
    · rename_i err _ ; cases hstep
    simp only [Except.ok.injEq] at hstep
    subst hstep
    intro k tf hget
    by_cases hkn : (name == k) = true
    · have hkEq : name = k := LawfulBEq.eq_of_beq hkn
      subst hkEq
      rw [IndexMap.getByKey_insert_self] at hget
      cases hget
    · have hne : (name == k) = false := Bool.not_eq_true _ |>.mp hkn
      rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
      exact hPacc k tf hget
  | constructor dt c =>
    unfold step4Lower at hstep
    simp only [bind, Except.bind, pure, Except.pure] at hstep
    split at hstep
    · rename_i err _ ; cases hstep
    split at hstep
    · rename_i err _ ; cases hstep
    simp only [Except.ok.injEq] at hstep
    subst hstep
    intro k tf hget
    by_cases hkn : (name == k) = true
    · have hkEq : name = k := LawfulBEq.eq_of_beq hkn
      subst hkEq
      rw [IndexMap.getByKey_insert_self] at hget
      cases hget
    · have hne : (name == k) = false := Bool.not_eq_true _ |>.mp hkn
      rw [IndexMap.getByKey_insert_of_beq_false _ _ hne] at hget
      exact hPacc k tf hget

/-- Composition modulo the drain-invariant `hnfFO_any_drained`: every
function produced by drain's specialization pipeline has FO output.
Caller at `CompilerCorrect.compile_correct` discharges this under
`FullyMonomorphic` (drain emits no new templates). -/
theorem concretize_preserves_FirstOrderReturn_of_drainInv
    {typedDecls : Typed.Decls} {concDecls : Concrete.Decls}
    (hP : Typed.Decls.FirstOrderReturn typedDecls)
    (hconc : typedDecls.concretize = .ok concDecls)
    (hnfFO_any_drained :
      ∀ drained, concretizeDrain typedDecls (concretizeDrainFuel typedDecls)
        { pending := concretizeSeed typedDecls, seen := {}, mono := {},
          newFunctions := #[], newDataTypes := #[] } = .ok drained →
        ∀ f ∈ drained.newFunctions, Typ.FirstOrder f.output) :
    ∀ g f, concDecls.getByKey g = some (.function f) →
           Concrete.Typ.FirstOrder f.output := by
  unfold Typed.Decls.concretize at hconc
  simp only [bind, Except.bind] at hconc
  split at hconc
  · rename_i err _ ; cases hconc
  rename_i drained hdrain
  have hnfFO := hnfFO_any_drained drained hdrain
  have hmdFO : ∀ g f,
      (concretizeBuild typedDecls drained.mono drained.newFunctions drained.newDataTypes).getByKey g
        = some (.function f) → Typ.FirstOrder f.output :=
    concretizeBuild_preserves_FirstOrderReturn hP hnfFO
  exact step4Lower_fold_preserves_FirstOrderReturn hmdFO hconc

/-! ### Drain `NewFunctionsFO` chain.

Closed under the auxiliary hypothesis `∀ g f, typedDecls.getByKey g = some
(.function f) → f.params = []`, which is implied by `FullyMonomorphic` via
`typedDecls_params_empty_of_fullyMonomorphic` in `CheckSound`. Under this
hypothesis, `mkParamSubst f.params args = fun _ => none`, so the subst-FO
side condition of `Typ.instantiate_preserves_FirstOrder` discharges
vacuously. -/

/-- `Typ.instantiate` preserves `Typ.FirstOrder`. Same shape as
`rewriteTyp_preserves_FirstOrder` minus the mono-map branch. -/
private theorem Typ.instantiate_preserves_FirstOrder
    (subst : Global → Option Typ) {t : Typ}
    (hsubstFO : ∀ g t', subst g = some t' → Typ.FirstOrder t')
    (hFO : Typ.FirstOrder t) :
    Typ.FirstOrder (Typ.instantiate subst t) := by
  induction hFO with
  | unit => unfold Typ.instantiate; exact .unit
  | field => unfold Typ.instantiate; exact .field
  | mvar n => unfold Typ.instantiate; exact .mvar n
  | ref g =>
    unfold Typ.instantiate
    cases hsub : subst g with
    | none => simp only [hsub, Option.getD_none]; exact .ref g
    | some t' =>
      simp only [hsub, Option.getD_some]
      exact hsubstFO g t' hsub
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
  | @app g args _ ih =>
    unfold Typ.instantiate
    refine .app ?_
    intro t' ht'
    obtain ⟨t0, ht0mem, ht0eq⟩ := mem_of_attach_map args _ ht'
    subst ht0eq
    exact ih t0 ht0mem

/-- `mkParamSubst []` is the empty substitution. -/
private theorem mkParamSubst_nil (args : Array Typ) :
    mkParamSubst [] args = fun _ => none := by
  funext g
  unfold mkParamSubst
  simp [List.zip_nil_left]

/-- Empty substitution is identity on `Typ`. Recursively unfolds through every
arm of `Typ.instantiate`; `attach.map` arms collapse via stdlib `pmap_eq_self`
+ `map_attach_eq_pmap`. -/
private theorem Typ.instantiate_empty_id : ∀ (t : Typ),
    Typ.instantiate (fun _ => none) t = t
  | .unit => by simp [Typ.instantiate]
  | .field => by simp [Typ.instantiate]
  | .mvar n => by simp [Typ.instantiate]
  | .ref g => by simp [Typ.instantiate]
  | .pointer t => by
      unfold Typ.instantiate
      rw [Typ.instantiate_empty_id t]
  | .array t n => by
      unfold Typ.instantiate
      rw [Typ.instantiate_empty_id t]
  | .tuple ts => by
      unfold Typ.instantiate
      congr 1
      rw [Array.map_attach_eq_pmap]
      apply Array.pmap_eq_self.mpr
      intro a ha
      exact Typ.instantiate_empty_id a
  | .app g args => by
      unfold Typ.instantiate
      congr 1
      rw [Array.map_attach_eq_pmap]
      apply Array.pmap_eq_self.mpr
      intro a ha
      exact Typ.instantiate_empty_id a
  | .function ins out => by
      unfold Typ.instantiate
      congr 1
      · rw [List.map_attach_eq_pmap]
        apply List.pmap_eq_self.mpr
        intro a ha
        exact Typ.instantiate_empty_id a
      · exact Typ.instantiate_empty_id out
  termination_by t => sizeOf t
  decreasing_by
    all_goals first
      | decreasing_tactic
      | (have := Array.sizeOf_lt_of_mem ha; grind)
      | (have := List.sizeOf_lt_of_mem ha; grind)

/-- Empty substitution is identity on typed terms. Mechanical 37-arm
structural induction; each arm dispatches to `Typ.instantiate_empty_id`
on type annotations + recursive `substInTypedTerm_empty_id` on subterms. -/
private theorem substInTypedTerm_empty_id : ∀ (t : Typed.Term),
    substInTypedTerm (fun _ => none) t = t
  | .unit τ e => by
      unfold substInTypedTerm; rw [Typ.instantiate_empty_id τ]
  | .var τ e x => by
      unfold substInTypedTerm; rw [Typ.instantiate_empty_id τ]
  | .ref τ e g tArgs => by
      unfold substInTypedTerm
      rw [Typ.instantiate_empty_id τ]
      congr 1
      -- Show `tArgs.map (Typ.instantiate (fun _ => none)) = tArgs` via toList.
      apply Array.toList_inj.mp
      simp only [Array.toList_map]
      induction tArgs.toList with
      | nil => rfl
      | cons hd tl ih =>
        simp only [List.map_cons]
        rw [Typ.instantiate_empty_id hd, ih]
  | .field τ e v => by
      unfold substInTypedTerm; rw [Typ.instantiate_empty_id τ]
  | .tuple τ e ts => by
      unfold substInTypedTerm
      rw [Typ.instantiate_empty_id τ]
      congr 1
      rw [Array.map_attach_eq_pmap]
      apply Array.pmap_eq_self.mpr
      intro a ha
      exact substInTypedTerm_empty_id a
  | .array τ e ts => by
      unfold substInTypedTerm
      rw [Typ.instantiate_empty_id τ]
      congr 1
      rw [Array.map_attach_eq_pmap]
      apply Array.pmap_eq_self.mpr
      intro a ha
      exact substInTypedTerm_empty_id a
  | .ret τ e r => by
      unfold substInTypedTerm
      rw [Typ.instantiate_empty_id τ, substInTypedTerm_empty_id r]
  | .let τ e p v b => by
      unfold substInTypedTerm
      rw [Typ.instantiate_empty_id τ, substInTypedTerm_empty_id v,
          substInTypedTerm_empty_id b]
  | .match τ e scrut bs => by
      unfold substInTypedTerm
      rw [Typ.instantiate_empty_id τ, substInTypedTerm_empty_id scrut]
      congr 1
      rw [List.map_attach_eq_pmap]
      apply List.pmap_eq_self.mpr
      intro ⟨p, b⟩ ha
      exact congrArg (Prod.mk p) (substInTypedTerm_empty_id b)
  | .app τ e g tArgs args u => by
      unfold substInTypedTerm
      rw [Typ.instantiate_empty_id τ]
      congr 1
      · -- Show `tArgs.map (Typ.instantiate (fun _ => none)) = tArgs` via toList.
        apply Array.toList_inj.mp
        simp only [Array.toList_map]
        induction tArgs.toList with
        | nil => rfl
        | cons hd tl ih =>
          simp only [List.map_cons]
          rw [Typ.instantiate_empty_id hd, ih]
      · rw [List.map_attach_eq_pmap]
        apply List.pmap_eq_self.mpr
        intro a ha
        exact substInTypedTerm_empty_id a
  | .add τ e a b => by
      unfold substInTypedTerm
      rw [Typ.instantiate_empty_id τ, substInTypedTerm_empty_id a,
          substInTypedTerm_empty_id b]
  | .sub τ e a b => by
      unfold substInTypedTerm
      rw [Typ.instantiate_empty_id τ, substInTypedTerm_empty_id a,
          substInTypedTerm_empty_id b]
  | .mul τ e a b => by
      unfold substInTypedTerm
      rw [Typ.instantiate_empty_id τ, substInTypedTerm_empty_id a,
          substInTypedTerm_empty_id b]
  | .eqZero τ e a => by
      unfold substInTypedTerm
      rw [Typ.instantiate_empty_id τ, substInTypedTerm_empty_id a]
  | .proj τ e a n => by
      unfold substInTypedTerm
      rw [Typ.instantiate_empty_id τ, substInTypedTerm_empty_id a]
  | .get τ e a n => by
      unfold substInTypedTerm
      rw [Typ.instantiate_empty_id τ, substInTypedTerm_empty_id a]
  | .slice τ e a i j => by
      unfold substInTypedTerm
      rw [Typ.instantiate_empty_id τ, substInTypedTerm_empty_id a]
  | .set τ e a n v => by
      unfold substInTypedTerm
      rw [Typ.instantiate_empty_id τ, substInTypedTerm_empty_id a,
          substInTypedTerm_empty_id v]
  | .store τ e a => by
      unfold substInTypedTerm
      rw [Typ.instantiate_empty_id τ, substInTypedTerm_empty_id a]
  | .load τ e a => by
      unfold substInTypedTerm
      rw [Typ.instantiate_empty_id τ, substInTypedTerm_empty_id a]
  | .ptrVal τ e a => by
      unfold substInTypedTerm
      rw [Typ.instantiate_empty_id τ, substInTypedTerm_empty_id a]
  | .assertEq τ e a b r => by
      unfold substInTypedTerm
      rw [Typ.instantiate_empty_id τ, substInTypedTerm_empty_id a,
          substInTypedTerm_empty_id b, substInTypedTerm_empty_id r]
  | .ioGetInfo τ e k => by
      unfold substInTypedTerm
      rw [Typ.instantiate_empty_id τ, substInTypedTerm_empty_id k]
  | .ioSetInfo τ e k i l r => by
      unfold substInTypedTerm
      rw [Typ.instantiate_empty_id τ, substInTypedTerm_empty_id k,
          substInTypedTerm_empty_id i, substInTypedTerm_empty_id l,
          substInTypedTerm_empty_id r]
  | .ioRead τ e i n => by
      unfold substInTypedTerm
      rw [Typ.instantiate_empty_id τ, substInTypedTerm_empty_id i]
  | .ioWrite τ e d r => by
      unfold substInTypedTerm
      rw [Typ.instantiate_empty_id τ, substInTypedTerm_empty_id d,
          substInTypedTerm_empty_id r]
  | .u8BitDecomposition τ e a => by
      unfold substInTypedTerm
      rw [Typ.instantiate_empty_id τ, substInTypedTerm_empty_id a]
  | .u8ShiftLeft τ e a => by
      unfold substInTypedTerm
      rw [Typ.instantiate_empty_id τ, substInTypedTerm_empty_id a]
  | .u8ShiftRight τ e a => by
      unfold substInTypedTerm
      rw [Typ.instantiate_empty_id τ, substInTypedTerm_empty_id a]
  | .u8Xor τ e a b => by
      unfold substInTypedTerm
      rw [Typ.instantiate_empty_id τ, substInTypedTerm_empty_id a,
          substInTypedTerm_empty_id b]
  | .u8Add τ e a b => by
      unfold substInTypedTerm
      rw [Typ.instantiate_empty_id τ, substInTypedTerm_empty_id a,
          substInTypedTerm_empty_id b]
  | .u8Sub τ e a b => by
      unfold substInTypedTerm
      rw [Typ.instantiate_empty_id τ, substInTypedTerm_empty_id a,
          substInTypedTerm_empty_id b]
  | .u8And τ e a b => by
      unfold substInTypedTerm
      rw [Typ.instantiate_empty_id τ, substInTypedTerm_empty_id a,
          substInTypedTerm_empty_id b]
  | .u8Or τ e a b => by
      unfold substInTypedTerm
      rw [Typ.instantiate_empty_id τ, substInTypedTerm_empty_id a,
          substInTypedTerm_empty_id b]
  | .u8LessThan τ e a b => by
      unfold substInTypedTerm
      rw [Typ.instantiate_empty_id τ, substInTypedTerm_empty_id a,
          substInTypedTerm_empty_id b]
  | .u32LessThan τ e a b => by
      unfold substInTypedTerm
      rw [Typ.instantiate_empty_id τ, substInTypedTerm_empty_id a,
          substInTypedTerm_empty_id b]
  | .debug τ e l t r => by
      unfold substInTypedTerm
      rw [Typ.instantiate_empty_id τ, substInTypedTerm_empty_id r]
      cases t with
      | none => rfl
      | some sub =>
        simp only
        rw [substInTypedTerm_empty_id sub]
  termination_by t => sizeOf t
  decreasing_by
    all_goals first
      | decreasing_tactic
      | (have : ∀ {α} [SizeOf α] (a : α), sizeOf a < sizeOf (some a) := by
           intros; show _ < 1 + _; omega
         grind)
      | (have hmem : _ ∈ _ := ‹_ ∈ _›
         have := Array.sizeOf_lt_of_mem hmem
         grind)
      | (have hmem : _ ∈ _ := ‹_ ∈ _›
         have := List.sizeOf_lt_of_mem hmem
         grind)

/-- Drain-state invariant: every new function has a first-order output. -/
private def DrainState.NewFunctionsFO (st : DrainState) : Prop :=
  ∀ f ∈ st.newFunctions, Typ.FirstOrder f.output

private theorem DrainState.NewFunctionsFO.init
    (pending : Std.HashSet (Global × Array Typ)) :
    DrainState.NewFunctionsFO
      { pending, seen := {}, mono := {}, newFunctions := #[], newDataTypes := #[] } := by
  intro f hf
  simp only [Array.not_mem_empty] at hf

private theorem concretizeDrainEntry_preserves_NewFunctionsFO
    {decls : Typed.Decls} (hP : Typed.Decls.FirstOrderReturn decls)
    (hparamsEmpty : ∀ g f, decls.getByKey g = some (.function f) → f.params = [])
    {state state' : DrainState}
    (hinv : DrainState.NewFunctionsFO state) (entry : Global × Array Typ)
    (hstep : concretizeDrainEntry decls state entry = .ok state') :
    DrainState.NewFunctionsFO state' := by
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
        intro f' hf'mem
        rcases Array.mem_push.mp hf'mem with hin | heq
        · exact hinv f' hin
        · subst heq
          simp only
          apply Typ.instantiate_preserves_FirstOrder
          · -- Under params = [], mkParamSubst [] _ = fun _ => none; hypothesis trivial.
            have hpe : f.params = [] := hparamsEmpty entry.1 f hf_get
            intro g t' hget
            rw [hpe, mkParamSubst_nil] at hget
            cases hget
          · exact hP entry.1 f hf_get
      · exact absurd hstep (by intro h; cases h)
    · rename_i dt hdt_get
      split at hstep
      · simp only [Except.ok.injEq] at hstep
        rw [← hstep]
        intro f hf; exact hinv f hf
      · exact absurd hstep (by intro h; cases h)
    · cases hstep

private theorem concretizeDrainEntry_list_foldlM_preserves_NewFunctionsFO
    {decls : Typed.Decls} (hP : Typed.Decls.FirstOrderReturn decls)
    (hparamsEmpty : ∀ g f, decls.getByKey g = some (.function f) → f.params = [])
    (L : List (Global × Array Typ))
    (state0 state' : DrainState)
    (hinv0 : DrainState.NewFunctionsFO state0)
    (hstep : L.foldlM (concretizeDrainEntry decls) state0 = .ok state') :
    DrainState.NewFunctionsFO state' := by
  induction L generalizing state0 with
  | nil =>
    simp only [List.foldlM, pure, Except.pure, Except.ok.injEq] at hstep
    rw [← hstep]; exact hinv0
  | cons hd tl ih =>
    simp only [List.foldlM, bind, Except.bind] at hstep
    split at hstep
    · cases hstep
    · rename_i s'' hs''
      have hinv1 : DrainState.NewFunctionsFO s'' :=
        concretizeDrainEntry_preserves_NewFunctionsFO hP hparamsEmpty hinv0 hd hs''
      exact ih s'' hinv1 hstep

private theorem concretizeDrainIter_preserves_NewFunctionsFO
    {decls : Typed.Decls} (hP : Typed.Decls.FirstOrderReturn decls)
    (hparamsEmpty : ∀ g f, decls.getByKey g = some (.function f) → f.params = [])
    {state state' : DrainState}
    (hinv : DrainState.NewFunctionsFO state)
    (hstep : concretizeDrainIter decls state = .ok state') :
    DrainState.NewFunctionsFO state' := by
  unfold concretizeDrainIter at hstep
  rw [← Array.foldlM_toList] at hstep
  let state0 : DrainState := { state with pending := ∅ }
  have hinv0 : DrainState.NewFunctionsFO state0 := hinv
  exact concretizeDrainEntry_list_foldlM_preserves_NewFunctionsFO hP hparamsEmpty
    state.pending.toArray.toList state0 state' hinv0 hstep

private theorem concretize_drain_preserves_NewFunctionsFO
    {decls : Typed.Decls} (hP : Typed.Decls.FirstOrderReturn decls)
    (hparamsEmpty : ∀ g f, decls.getByKey g = some (.function f) → f.params = [])
    (fuel : Nat) (init : DrainState)
    (hinv : DrainState.NewFunctionsFO init)
    {drained : DrainState}
    (hdrain : concretizeDrain decls fuel init = .ok drained) :
    DrainState.NewFunctionsFO drained := by
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
        have hinv' : DrainState.NewFunctionsFO state' :=
          concretizeDrainIter_preserves_NewFunctionsFO hP hparamsEmpty hinv hstate'
        exact ih state' hinv' hdrain

/-- **Main bridge (C): `Typed.Decls.FirstOrderReturn` ⇒
`Concrete.Decls.FirstOrderReturn`.** Caller-facing form.

Strengthened sig: takes a `params = []` hypothesis covering every function
in `typedDecls`. This lets us close the drain-invariant
(`∀ f ∈ drained.newFunctions, Typ.FirstOrder f.output`): when `f.params = []`,
`mkParamSubst f.params args = fun _ => none`, and the substitution-FO side
condition of `Typ.instantiate_preserves_FirstOrder` is vacuous.

The caller dispatches the `params = []` hypothesis from
`hwf.fullyMonomorphic` via `typedDecls_params_empty_of_fullyMonomorphic`. -/
theorem concretize_preserves_FirstOrderReturn
    {typedDecls : Typed.Decls} {concDecls : Concrete.Decls}
    (hP : Typed.Decls.FirstOrderReturn typedDecls)
    (hparamsEmpty : ∀ g f, typedDecls.getByKey g = some (.function f) → f.params = [])
    (hconc : typedDecls.concretize = .ok concDecls) :
    Concrete.Decls.FirstOrderReturn concDecls := by
  intro g f hget
  apply concretize_preserves_FirstOrderReturn_of_drainInv hP hconc _ g f hget
  intro drained hdrain f' hfmem
  have hinit := DrainState.NewFunctionsFO.init (concretizeSeed typedDecls)
  exact concretize_drain_preserves_NewFunctionsFO hP hparamsEmpty _ _ hinit hdrain f' hfmem

/-! ### `TermRefsDt` bridge infrastructure.

Mirrors the FO chain above. The two structural 37-arm lemmas are the heart
(`rewriteTypedTerm_preserves_RefsDt` on typed→typed rewrite,
`termToConcrete_preserves_RefsDt` on typed→concrete lowering); the
composition layers (`concretizeBuild`, `step4Lower` fold) assemble them. -/

/-- List-level analogue of `mem_of_attach_map`. -/
private theorem list_mem_of_attach_map {α β : Type _}
    (l : List α) (f : {x // x ∈ l} → β) {b : β}
    (h : b ∈ l.attach.map f) :
    ∃ (a : α) (ha : a ∈ l), f ⟨a, ha⟩ = b := by
  rw [List.mem_map] at h
  obtain ⟨⟨a, ha⟩, _hmem, hfeq⟩ := h
  exact ⟨a, ha, hfeq⟩

-- `List.mem_mapM_ok_forall` is already defined inline above.

/-- `rewriteTypedTerm` preserves `Typed.Term.RefsDt` structurally.
Given bridges from the source decls table into the target `tds'` (typed-side)
for dt/ctor keys, and a `rewriteGlobal` preservation witness, each arm
rebuilds `RefsDt tds'` on the rewritten term. -/
private theorem rewriteTypedTerm_preserves_RefsDt
    {decls : Typed.Decls} {subst : Global → Option Typ} {mono : MonoMap}
    {tds' : Typed.Decls} {body : Typed.Term}
    (hbody : Typed.Term.RefsDt decls body)
    (hdt_bridge : ∀ g, (∃ dt, decls.getByKey g = some (.dataType dt)) →
      ∃ dt', tds'.getByKey g = some (.dataType dt'))
    (hctor_bridge : ∀ g, (∃ dt c, decls.getByKey g = some (.constructor dt c)) →
      ∃ dt' c', tds'.getByKey g = some (.constructor dt' c'))
    (hrewriteGlobal_preserve : ∀ g tArgs,
      ((∃ dt, decls.getByKey g = some (.dataType dt)) ∨
       (∃ dt c, decls.getByKey g = some (.constructor dt c))) →
      (∃ dt, decls.getByKey (rewriteGlobal decls mono g tArgs) = some (.dataType dt)) ∨
      (∃ dt c, decls.getByKey (rewriteGlobal decls mono g tArgs) = some (.constructor dt c))) :
    Typed.Term.RefsDt tds' (rewriteTypedTerm decls subst mono body) := by
  induction hbody with
  | unit => unfold rewriteTypedTerm; exact .unit
  | var => unfold rewriteTypedTerm; exact .var
  | @ref typ e g tArgs hdt =>
    unfold rewriteTypedTerm
    refine .ref ?_
    rcases hrewriteGlobal_preserve g tArgs hdt with ⟨dt, hdt'⟩ | ⟨dt, c, hctor⟩
    · exact Or.inl (hdt_bridge _ ⟨dt, hdt'⟩)
    · exact Or.inr (hctor_bridge _ ⟨dt, c, hctor⟩)
  | field => unfold rewriteTypedTerm; exact .field
  | @tuple typ e ts _ ih =>
    unfold rewriteTypedTerm
    refine .tuple ?_
    intro sub hsub
    obtain ⟨t0, ht0mem, ht0eq⟩ := mem_of_attach_map ts _ hsub
    subst ht0eq
    exact ih t0 ht0mem
  | @array typ e ts _ ih =>
    unfold rewriteTypedTerm
    refine .array ?_
    intro sub hsub
    obtain ⟨t0, ht0mem, ht0eq⟩ := mem_of_attach_map ts _ hsub
    subst ht0eq
    exact ih t0 ht0mem
  | ret _ ihr =>
    unfold rewriteTypedTerm; exact .ret ihr
  | «let» _ _ ihv ihb =>
    unfold rewriteTypedTerm; exact .let ihv ihb
  | @«match» typ e scrut cases _ _ ihscrut ihcases =>
    unfold rewriteTypedTerm
    refine .match ihscrut ?_
    intro pc hpc
    obtain ⟨p0, hp0mem, hp0eq⟩ := list_mem_of_attach_map cases _ hpc
    subst hp0eq
    exact ihcases p0 hp0mem
  | @app typ e g tArgs args u _ ih =>
    unfold rewriteTypedTerm
    refine .app ?_
    intro a ha
    obtain ⟨a0, ha0mem, ha0eq⟩ := list_mem_of_attach_map args _ ha
    subst ha0eq
    exact ih a0 ha0mem
  | add _ _ iha ihb => unfold rewriteTypedTerm; exact .add iha ihb
  | sub _ _ iha ihb => unfold rewriteTypedTerm; exact .sub iha ihb
  | mul _ _ iha ihb => unfold rewriteTypedTerm; exact .mul iha ihb
  | eqZero _ iha => unfold rewriteTypedTerm; exact .eqZero iha
  | proj _ iha => unfold rewriteTypedTerm; exact .proj iha
  | get _ iha => unfold rewriteTypedTerm; exact .get iha
  | slice _ iha => unfold rewriteTypedTerm; exact .slice iha
  | «set» _ _ iha ihv => unfold rewriteTypedTerm; exact .set iha ihv
  | store _ iha => unfold rewriteTypedTerm; exact .store iha
  | load _ iha => unfold rewriteTypedTerm; exact .load iha
  | ptrVal _ iha => unfold rewriteTypedTerm; exact .ptrVal iha
  | assertEq _ _ _ iha ihb ihr =>
    unfold rewriteTypedTerm; exact .assertEq iha ihb ihr
  | ioGetInfo _ ihk => unfold rewriteTypedTerm; exact .ioGetInfo ihk
  | ioSetInfo _ _ _ _ ihk ihi ihl ihr =>
    unfold rewriteTypedTerm; exact .ioSetInfo ihk ihi ihl ihr
  | ioRead _ ihi => unfold rewriteTypedTerm; exact .ioRead ihi
  | ioWrite _ _ ihd ihr => unfold rewriteTypedTerm; exact .ioWrite ihd ihr
  | u8BitDecomposition _ iha => unfold rewriteTypedTerm; exact .u8BitDecomposition iha
  | u8ShiftLeft _ iha => unfold rewriteTypedTerm; exact .u8ShiftLeft iha
  | u8ShiftRight _ iha => unfold rewriteTypedTerm; exact .u8ShiftRight iha
  | u8Xor _ _ iha ihb => unfold rewriteTypedTerm; exact .u8Xor iha ihb
  | u8Add _ _ iha ihb => unfold rewriteTypedTerm; exact .u8Add iha ihb
  | u8Sub _ _ iha ihb => unfold rewriteTypedTerm; exact .u8Sub iha ihb
  | u8And _ _ iha ihb => unfold rewriteTypedTerm; exact .u8And iha ihb
  | u8Or  _ _ iha ihb => unfold rewriteTypedTerm; exact .u8Or iha ihb
  | u8LessThan  _ _ iha ihb => unfold rewriteTypedTerm; exact .u8LessThan iha ihb
  | u32LessThan _ _ iha ihb => unfold rewriteTypedTerm; exact .u32LessThan iha ihb
  | @debug typ e label t r ht hr iht ihr =>
    unfold rewriteTypedTerm
    refine .debug ?_ ihr
    intro tval htval
    cases t with
    | none => cases htval
    | some sub =>
      simp only [Option.some.injEq] at htval
      subst htval
      exact iht sub rfl


/-! #### `Concrete.Term.RefsDt` monotonicity.

Under an "all-keys-preserving" hypothesis on the underlying `Concrete.Decls`,
`RefsDt cd₁ t → RefsDt cd₂ t`. The pipeline only ever inserts new entries
into the accumulator (no key deletion or function-key injection over a
prior dt/ctor-keyed entry), so the witness for each `.ref` subterm survives
through every step. -/
private theorem Concrete.Term.RefsDt.mono
    {cd₁ cd₂ : Concrete.Decls} {t : Concrete.Term}
    (hwit : ∀ g,
      ((∃ dt, cd₁.getByKey g = some (.dataType dt)) ∨
       (∃ dt c, cd₁.getByKey g = some (.constructor dt c))) →
      ((∃ dt, cd₂.getByKey g = some (.dataType dt)) ∨
       (∃ dt c, cd₂.getByKey g = some (.constructor dt c))))
    (hr : Concrete.Term.RefsDt cd₁ t) :
    Concrete.Term.RefsDt cd₂ t := by
  induction hr with
  | unit => exact .unit
  | var => exact .var
  | ref hdt => exact .ref (hwit _ hdt)
  | field => exact .field
  | tuple _ ih => exact .tuple ih
  | array _ ih => exact .array ih
  | ret _ ih => exact .ret ih
  | letVar _ _ ihv ihb => exact .letVar ihv ihb
  | letWild _ _ ihv ihb => exact .letWild ihv ihb
  | letLoad _ ihb => exact .letLoad ihb
  | «match» _ _ ihcases ihdef => exact .match ihcases ihdef
  | app _ ih => exact .app ih
  | add _ _ iha ihb => exact .add iha ihb
  | sub _ _ iha ihb => exact .sub iha ihb
  | mul _ _ iha ihb => exact .mul iha ihb
  | eqZero _ ih => exact .eqZero ih
  | proj _ ih => exact .proj ih
  | get _ ih => exact .get ih
  | slice _ ih => exact .slice ih
  | «set» _ _ iha ihv => exact .set iha ihv
  | store _ ih => exact .store ih
  | load _ ih => exact .load ih
  | ptrVal _ ih => exact .ptrVal ih
  | assertEq _ _ _ iha ihb ihr => exact .assertEq iha ihb ihr
  | ioGetInfo _ ih => exact .ioGetInfo ih
  | ioSetInfo _ _ _ _ ihk ihi ihl ihr => exact .ioSetInfo ihk ihi ihl ihr
  | ioRead _ ih => exact .ioRead ih
  | ioWrite _ _ ihd ihr => exact .ioWrite ihd ihr
  | u8BitDecomposition _ ih => exact .u8BitDecomposition ih
  | u8ShiftLeft _ ih => exact .u8ShiftLeft ih
  | u8ShiftRight _ ih => exact .u8ShiftRight ih
  | u8Xor _ _ iha ihb => exact .u8Xor iha ihb
  | u8Add _ _ iha ihb => exact .u8Add iha ihb
  | u8Sub _ _ iha ihb => exact .u8Sub iha ihb
  | u8And _ _ iha ihb => exact .u8And iha ihb
  | u8Or _ _ iha ihb => exact .u8Or iha ihb
  | u8LessThan _ _ iha ihb => exact .u8LessThan iha ihb
  | u32LessThan _ _ iha ihb => exact .u32LessThan iha ihb
  | debug _ _ iht ihr => exact .debug iht ihr

/-- `destructureTuple` preserves `RefsDt cb` on its output. The output is a
foldl over `List.range pats.size`, each step wrapping the accumulator in
`.letVar`/`.letWild` over a `.proj` on `scrutTerm`. Both wrappers are
constructors of `Concrete.Term.RefsDt` whose only inductive premise is
`RefsDt acc`, plus the trivially-`RefsDt` `.proj` on the (RefsDt) scrutinee. -/
private theorem destructureTuple_preserves_RefsDt
    {cd : Concrete.Decls}
    (scrutTerm : Concrete.Term) (pats : Array Pattern)
    (ts : Array Concrete.Typ) (cb : Concrete.Term)
    (hscrut : Concrete.Term.RefsDt cd scrutTerm)
    (hcb : Concrete.Term.RefsDt cd cb) :
    Concrete.Term.RefsDt cd (destructureTuple scrutTerm pats ts cb) := by
  unfold destructureTuple
  induction (List.range pats.size) generalizing cb with
  | nil => simpa using hcb
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    apply ih
    -- The single-step body wraps cb in either .letVar or .letWild over .proj scrutTerm.
    have hproj : Concrete.Term.RefsDt cd
        (.proj (ts[pats.size - 1 - hd]?.getD .unit) false scrutTerm
          (pats.size - 1 - hd)) := .proj hscrut
    split <;> first
      | exact .letVar hproj hcb
      | exact .letWild hproj hcb

/-- `destructureArray` preserves `RefsDt cb` on its output. Same shape as
`destructureTuple_preserves_RefsDt`, with `.get` in place of `.proj`. -/
private theorem destructureArray_preserves_RefsDt
    {cd : Concrete.Decls}
    (scrutTerm : Concrete.Term) (pats : Array Pattern)
    (eltTyp : Concrete.Typ) (cb : Concrete.Term)
    (hscrut : Concrete.Term.RefsDt cd scrutTerm)
    (hcb : Concrete.Term.RefsDt cd cb) :
    Concrete.Term.RefsDt cd (destructureArray scrutTerm pats eltTyp cb) := by
  unfold destructureArray
  induction (List.range pats.size) generalizing cb with
  | nil => simpa using hcb
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    apply ih
    have hget : Concrete.Term.RefsDt cd
        (.get eltTyp false scrutTerm (pats.size - 1 - hd)) := .get hscrut
    split <;> first
      | exact .letVar hget hcb
      | exact .letWild hget hcb

/-- Sub-lemma for the general `.match` path: `expandPattern` produces a
list of cases each of whose body is either `cb` itself, or `cb` wrapped in
a `.letVar _ _ x (.var scrutTyp false scrutLocal) cb`. In both cases, if
`Concrete.Term.RefsDt cd cb`, then every produced body satisfies
`Concrete.Term.RefsDt cd`. Recurses on Pattern for the `.or` case. -/
private theorem expandPattern_preserves_RefsDt
    {cd : Concrete.Decls} {scrutTyp : Concrete.Typ} {scrutLocal : Local} :
    ∀ {p : Pattern} {cb : Concrete.Term}
      {result : Array (Concrete.Pattern × Concrete.Term)},
      Concrete.Term.RefsDt cd cb →
      expandPattern scrutTyp scrutLocal p cb = .ok result →
      ∀ pc ∈ result, Concrete.Term.RefsDt cd pc.2
  | .wildcard, cb, result, hcb, hexp => by
    unfold expandPattern at hexp
    simp only [pure, Except.pure, Except.ok.injEq] at hexp
    subst hexp
    intro pc hpc
    have hpc' : pc = (.wildcard, cb) := by simpa using hpc
    subst hpc'; exact hcb
  | .var x, cb, result, hcb, hexp => by
    unfold expandPattern at hexp
    simp only [pure, Except.pure, Except.ok.injEq] at hexp
    subst hexp
    intro pc hpc
    have hpc' : pc = (.wildcard,
        .letVar cb.typ cb.escapes x (.var scrutTyp false scrutLocal) cb) := by
      simpa using hpc
    subst hpc'
    exact .letVar .var hcb
  | .field g, cb, result, hcb, hexp => by
    unfold expandPattern at hexp
    simp only [pure, Except.pure, Except.ok.injEq] at hexp
    subst hexp
    intro pc hpc
    have hpc' : pc = (.field g, cb) := by simpa using hpc
    subst hpc'; exact hcb
  | .ref g pats, cb, result, hcb, hexp => by
    unfold expandPattern at hexp
    simp only [bind, Except.bind, pure, Except.pure] at hexp
    split at hexp
    · cases hexp
    rename_i locals _hloc
    simp only [Except.ok.injEq] at hexp
    subst hexp
    intro pc hpc
    have hpc' : pc = (.ref g locals, cb) := by simpa using hpc
    subst hpc'; exact hcb
  | .tuple pats, cb, result, hcb, hexp => by
    unfold expandPattern at hexp
    simp only [bind, Except.bind, pure, Except.pure] at hexp
    split at hexp
    · cases hexp
    rename_i locals _hloc
    simp only [Except.ok.injEq] at hexp
    subst hexp
    intro pc hpc
    have hpc' : pc = (.tuple locals, cb) := by simpa using hpc
    subst hpc'; exact hcb
  | .array pats, cb, result, hcb, hexp => by
    unfold expandPattern at hexp
    simp only [bind, Except.bind, pure, Except.pure] at hexp
    split at hexp
    · cases hexp
    rename_i locals _hloc
    simp only [Except.ok.injEq] at hexp
    subst hexp
    intro pc hpc
    have hpc' : pc = (.array locals, cb) := by simpa using hpc
    subst hpc'; exact hcb
  | .or p1 p2, cb, result, hcb, hexp => by
    unfold expandPattern at hexp
    simp only [bind, Except.bind, pure, Except.pure] at hexp
    split at hexp
    · cases hexp
    rename_i r1 hr1
    split at hexp
    · cases hexp
    rename_i r2 hr2
    simp only [Except.ok.injEq] at hexp
    subst hexp
    intro pc hpc
    rw [Array.mem_append] at hpc
    rcases hpc with h1 | h2
    · exact expandPattern_preserves_RefsDt hcb hr1 pc h1
    · exact expandPattern_preserves_RefsDt hcb hr2 pc h2
  | .pointer p, cb, result, _hcb, hexp => by
    -- Throws .unsupportedPattern; hexp is unreachable.
    unfold expandPattern at hexp
    cases hexp

/-- Generic `foldlM` invariant for the `attach`-folded `expandPattern` builder.
Given a list `xs : List _` (with each element memorized in `bs` via `hsub`),
folding `expandPattern scrutTyp scrutLocal x.val.1 cb_x` (where
`cb_x = (termToConcrete mono x.val.2).ok`) over `xs_attach` produces an array
where every case body satisfies `RefsDt cd`. -/
private theorem expandPattern_foldlM_preserves_RefsDt
    {cd : Concrete.Decls}
    {mono : Std.HashMap (Global × Array Typ) Global}
    {scrutTyp : Concrete.Typ} {scrutLocal : Local}
    (bs : List (Pattern × Typed.Term))
    (ihcases : ∀ pc ∈ bs, ∀ {cb},
      termToConcrete mono pc.2 = .ok cb → Concrete.Term.RefsDt cd cb) :
    ∀ (xs_attach : List (Pattern × Typed.Term))
      (init final : Array (Concrete.Pattern × Concrete.Term)),
      (∀ x ∈ xs_attach, x ∈ bs) →
      (∀ pc' ∈ init, Concrete.Term.RefsDt cd pc'.2) →
      List.foldlM
        (fun acc (x : Pattern × Typed.Term) => do
          let cb ← termToConcrete mono x.2
          pure (acc ++ (← expandPattern scrutTyp scrutLocal x.1 cb)))
        init xs_attach = .ok final →
      ∀ pc' ∈ final, Concrete.Term.RefsDt cd pc'.2
  | [], init, final, _hsub, hinit, hfold => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at hfold
    subst hfold
    exact hinit
  | hd :: tl, init, final, hsub, hinit, hfold => by
    rw [List.foldlM_cons] at hfold
    simp only [bind, Except.bind] at hfold
    -- Now hfold has the shape `(termToConcrete mono hd.2 >>= fun cb => ...)`.
    cases hcb_hd : termToConcrete mono hd.2 with
    | error _ => rw [hcb_hd] at hfold; cases hfold
    | ok cb_hd =>
      rw [hcb_hd] at hfold
      simp only at hfold
      cases hexp_hd : expandPattern scrutTyp scrutLocal hd.1 cb_hd with
      | error _ => rw [hexp_hd] at hfold; cases hfold
      | ok exp_hd =>
        rw [hexp_hd] at hfold
        simp only [pure, Except.pure] at hfold
        have hd_in_bs : hd ∈ bs := hsub hd List.mem_cons_self
        have hcb_ref : Concrete.Term.RefsDt cd cb_hd :=
          ihcases hd hd_in_bs hcb_hd
        have hexp_good : ∀ pc' ∈ exp_hd, Concrete.Term.RefsDt cd pc'.2 :=
          expandPattern_preserves_RefsDt hcb_ref hexp_hd
        have hnew_init : ∀ pc' ∈ init ++ exp_hd, Concrete.Term.RefsDt cd pc'.2 := by
          intro pc' hpc'
          rw [Array.mem_append] at hpc'
          rcases hpc' with h | h
          · exact hinit pc' h
          · exact hexp_good pc' h
        have hsub_tl : ∀ x ∈ tl, x ∈ bs :=
          fun x hx => hsub x (List.mem_cons_of_mem _ hx)
        exact expandPattern_foldlM_preserves_RefsDt bs ihcases tl
          (init ++ exp_hd) final hsub_tl hnew_init hfold

/-- Helper for the `.match` arm of `termToConcrete_preserves_RefsDt`. The
arm takes 3 paths (single-tuple irrefutable / single-array irrefutable /
general expandPattern fold). All produce concrete terms whose RefsDt
reduces to the body's RefsDt; the IHs `ihscrut` and `ihcases` provide
RefsDt for the recursively-lowered scrut/branch bodies.

Sub-paths (a) `destructureTuple` and (b) `destructureArray` are F=0 via
`destructureTuple_preserves_RefsDt` / `destructureArray_preserves_RefsDt`
helpers above. Sub-path (c) (general fold) is F=0 via
`expandPattern_preserves_RefsDt` + `expandPattern_foldlM_preserves_RefsDt`.
The `match`-arm dispatch composing them is F=1 below. -/
private theorem termToConcrete_match_arm_preserves_RefsDt
    {tds : Typed.Decls} {cd : Concrete.Decls}
    {mono : Std.HashMap (Global × Array Typ) Global}
    {cbody : Concrete.Term}
    (typ : Typ) (e : Bool) (scrut : Typed.Term) (bs : List (Pattern × Typed.Term))
    (_hwit : ∀ g,
      ((∃ dt, tds.getByKey g = some (.dataType dt)) ∨
       (∃ dt c, tds.getByKey g = some (.constructor dt c))) →
      ((∃ dt, cd.getByKey g = some (.dataType dt)) ∨
       (∃ dt c, cd.getByKey g = some (.constructor dt c))))
    (ihscrut : ∀ {cs}, termToConcrete mono scrut = .ok cs → Concrete.Term.RefsDt cd cs)
    (ihcases : ∀ pc ∈ bs, ∀ {cb},
      termToConcrete mono pc.2 = .ok cb → Concrete.Term.RefsDt cd cb)
    (hrun : termToConcrete mono (.match typ e scrut bs) = .ok cbody) :
    Concrete.Term.RefsDt cd cbody := by
  -- Unfold the .match arm of termToConcrete and reduce the do-bind cascade.
  unfold termToConcrete at hrun
  simp only [bind, Except.bind, pure, Except.pure] at hrun
  split at hrun
  · cases hrun
  rename_i τ' _hτ
  split at hrun
  · cases hrun
  rename_i scrut' hscrut'
  -- scrut' must be a `.var ...` else `unsupportedMatchScrutinee` is thrown.
  split at hrun
  rotate_left
  · cases hrun
  rename_i _scrutTerm sty esc sl
  -- After this rename:
  --  sty : Concrete.Typ (typ of `.var`); esc : Bool (escape); sl : Local
  --  hscrut' : termToConcrete mono scrut = Except.ok (.var sty esc sl).
  -- The first split corresponds to:
  --   `match bs with | [(.tuple body_t, hbs_eq)] => <inner: match sty with | .tuple ts => ...> | _ => ...`
  split at hrun
  · -- bs = [(.tuple body_t, hbs_eq)].
    rename_i _orphan body_t hbs_eq
    -- Inner split: match sty with | .tuple ts => ... | _ => fallthrough.
    split at hrun
    · -- sty = .tuple ts.  hrun has `match termToConcrete mono hbs_eq with ...`
      rename_i ts
      split at hrun
      · cases hrun
      rename_i cb hcb
      simp only [Except.ok.injEq] at hrun
      subst hrun
      have hbs_mem : ((Pattern.tuple body_t, hbs_eq) : Pattern × Typed.Term)
          ∈ [(Pattern.tuple body_t, hbs_eq)] := List.mem_singleton.mpr rfl
      have hcbR : Concrete.Term.RefsDt cd cb := ihcases _ hbs_mem hcb
      have hscrutTermR : Concrete.Term.RefsDt cd
          (.var (Concrete.Typ.tuple ts) false sl) := .var
      exact destructureTuple_preserves_RefsDt _ body_t ts cb hscrutTermR hcbR
    · -- sty ≠ .tuple. Fallthrough.
      -- The inner match `[(P.tuple body_t, hbs_eq)] vs [(P.array ...)] is the wildcard.
      split at hrun
      · -- The "fired" array-singleton arm — contradiction:
        -- [(P.tuple body_t, hbs_eq)] = [(P.array pats, body)] forces tuple = array.
        rename_i _ _ _ _ habs
        simp only [List.cons.injEq, Prod.mk.injEq] at habs
        obtain ⟨⟨hp, _⟩, _⟩ := habs
        cases hp
      · -- Wildcard arm matched: hrun has the general foldlM path.
        split at hrun
        · cases hrun
        rename_i cases' hcases'
        simp only [Except.ok.injEq] at hrun
        subst hrun
        refine .match ?_ (fun d hd => by cases hd)
        rw [← Array.foldlM_toList, Array.toList_attach] at hcases'
        intro pc hpc
        exact expandPattern_foldlM_preserves_RefsDt
          [(Pattern.tuple body_t, hbs_eq)] ihcases
          [(Pattern.tuple body_t, hbs_eq)] #[] cases'
          (fun x hx => hx) (by intro pc' hpc'; simp at hpc') hcases' pc hpc
  · -- bs is NOT single-tuple-with-tuple-sty arm. Try array-singleton arm.
    split at hrun
    · -- bs = [(.array pats_a, body_a)]. 4 anonymous vars introduced.
      -- Trace state shows: bs✝ (orphan), _o1 (orphan), pats✝ (Array Pattern),
      -- body✝ (Typed.Term), then the negation hypothesis.
      rename_i _o1 _o2 pats_a body_a _hneg_tup
      split at hrun
      · -- sty = .array eltTyp n.
        rename_i eltTyp n
        split at hrun
        · cases hrun
        rename_i cb hcb
        simp only [Except.ok.injEq] at hrun
        subst hrun
        have hbs_mem : ((Pattern.array pats_a, body_a) : Pattern × Typed.Term)
            ∈ [(Pattern.array pats_a, body_a)] := List.mem_singleton.mpr rfl
        have hcbR : Concrete.Term.RefsDt cd cb := ihcases _ hbs_mem hcb
        have hscrutTermR : Concrete.Term.RefsDt cd
            (.var (Concrete.Typ.array eltTyp n) false sl) := .var
        exact destructureArray_preserves_RefsDt _ pats_a eltTyp cb hscrutTermR hcbR
      · -- sty ≠ .array. Fallthrough to general fold.
        split at hrun
        · cases hrun
        rename_i cases' hcases'
        simp only [Except.ok.injEq] at hrun
        subst hrun
        refine .match ?_ (fun d hd => by cases hd)
        rw [← Array.foldlM_toList, Array.toList_attach] at hcases'
        intro pc hpc
        exact expandPattern_foldlM_preserves_RefsDt
          [(Pattern.array pats_a, body_a)] ihcases
          [(Pattern.array pats_a, body_a)] #[] cases'
          (fun x hx => hx) (by intro pc' hpc'; simp at hpc') hcases' pc hpc
    · -- bs is NOT single-tuple AND NOT single-array. General path.
      split at hrun
      · cases hrun
      rename_i cases' hcases'
      simp only [Except.ok.injEq] at hrun
      subst hrun
      refine .match ?_ (fun d hd => by cases hd)
      rw [← Array.foldlM_toList] at hcases'
      intro pc hpc
      -- The fold uses an `attachWith` over bs.toArray; bridge via a foldlM equation
      -- that drops the subtype to the plain (Pattern × Typed.Term) shape.
      -- Build an `ihcases` for `bs.toArray.toList` (= bs), then apply the helper
      -- specialised to the attachWith subtype.
      let f_attach : Array (Concrete.Pattern × Concrete.Term) →
          { x // x ∈ bs.toArray } → Except ConcretizeError (Array (Concrete.Pattern × Concrete.Term)) :=
        fun acc y => do
          let cb ← termToConcrete mono y.1.snd
          let exp ← expandPattern sty sl y.1.fst cb
          pure (acc ++ exp)
      -- Recurse over the attachWith list.
      have key : ∀ (xs : List { x // x ∈ bs.toArray })
            (init final : Array (Concrete.Pattern × Concrete.Term)),
          (∀ pc' ∈ init, Concrete.Term.RefsDt cd pc'.2) →
          List.foldlM f_attach init xs = .ok final →
          ∀ pc' ∈ final, Concrete.Term.RefsDt cd pc'.2 := by
        intro xs
        induction xs with
        | nil =>
          intro init final hinit hfold
          simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at hfold
          subst hfold; exact hinit
        | cons hd tl ih =>
          intro init final hinit hfold
          rw [List.foldlM_cons] at hfold
          simp only [bind, Except.bind, f_attach] at hfold
          cases hcb_hd : termToConcrete mono hd.1.2 with
          | error _ => rw [hcb_hd] at hfold; cases hfold
          | ok cb_hd =>
            rw [hcb_hd] at hfold
            simp only at hfold
            cases hexp_hd : expandPattern sty sl hd.1.1 cb_hd with
            | error _ => rw [hexp_hd] at hfold; cases hfold
            | ok exp_hd =>
              rw [hexp_hd] at hfold
              simp only [pure, Except.pure] at hfold
              have hd_in_bs : hd.1 ∈ bs := by
                have := hd.2
                simpa using this
              have hcb_ref : Concrete.Term.RefsDt cd cb_hd :=
                ihcases _ hd_in_bs hcb_hd
              have hexp_good : ∀ pc' ∈ exp_hd, Concrete.Term.RefsDt cd pc'.2 :=
                expandPattern_preserves_RefsDt hcb_ref hexp_hd
              have hnew_init : ∀ pc' ∈ init ++ exp_hd, Concrete.Term.RefsDt cd pc'.2 := by
                intro pc' hpc'
                rw [Array.mem_append] at hpc'
                rcases hpc' with h | h
                · exact hinit pc' h
                · exact hexp_good pc' h
              exact ih _ _ hnew_init hfold
      exact key _ #[] cases' (by intro pc' hpc'; simp at hpc') hcases' pc hpc

/-! #### `termToConcrete` preserves `RefsDt`.

Structural pass: every typed `Typed.Term.RefsDt tds body` whose
`.ref g` witnesses survive into `cd` (via `hwit`) lifts to
`Concrete.Term.RefsDt cd (termToConcrete mono body)`. The `mono` argument
only affects `typToConcrete` (type lowering), which doesn't influence
`RefsDt` — only term-level `.ref g` arms matter. -/
private theorem termToConcrete_preserves_RefsDt
    {tds : Typed.Decls} {cd : Concrete.Decls}
    {mono : Std.HashMap (Global × Array Typ) Global}
    {body : Typed.Term} {cbody : Concrete.Term}
    (hbody : Typed.Term.RefsDt tds body)
    (hwit : ∀ g,
      ((∃ dt, tds.getByKey g = some (.dataType dt)) ∨
       (∃ dt c, tds.getByKey g = some (.constructor dt c))) →
      ((∃ dt, cd.getByKey g = some (.dataType dt)) ∨
       (∃ dt c, cd.getByKey g = some (.constructor dt c))))
    (hrun : termToConcrete mono body = .ok cbody) :
    Concrete.Term.RefsDt cd cbody := by
  induction hbody generalizing cbody with
  | unit =>
    unfold termToConcrete at hrun
    simp only [bind, Except.bind, pure, Except.pure] at hrun
    split at hrun
    · cases hrun
    rename_i τ' _hτ
    simp only [Except.ok.injEq] at hrun
    subst hrun
    exact .unit
  | var =>
    unfold termToConcrete at hrun
    simp only [bind, Except.bind, pure, Except.pure] at hrun
    split at hrun
    · cases hrun
    rename_i τ' _hτ
    simp only [Except.ok.injEq] at hrun
    subst hrun
    exact .var
  | @ref typ e g tArgs hdt =>
    unfold termToConcrete at hrun
    simp only [bind, Except.bind, pure, Except.pure] at hrun
    split at hrun
    · cases hrun
    rename_i τ' _hτ
    simp only [Except.ok.injEq] at hrun
    subst hrun
    exact .ref (hwit g hdt)
  | field =>
    unfold termToConcrete at hrun
    simp only [bind, Except.bind, pure, Except.pure] at hrun
    split at hrun
    · cases hrun
    rename_i τ' _hτ
    simp only [Except.ok.injEq] at hrun
    subst hrun
    exact .field
  | @tuple typ e ts _hts ih =>
    unfold termToConcrete at hrun
    simp only [bind, Except.bind, pure, Except.pure] at hrun
    split at hrun
    · cases hrun
    rename_i τ' _hτ
    split at hrun
    · cases hrun
    rename_i ts' hts'
    simp only [Except.ok.injEq] at hrun
    subst hrun
    refine .tuple ?_
    intro sub hsub
    exact Array.mem_mapM_ok_forall
      (P := fun x => x ∈ ts) (Q := Concrete.Term.RefsDt cd)
      (fun x hxMem fx hfx => ih x hxMem hfx) ts ts' (fun x hx => hx) hts' sub hsub
  | @array typ e ts _hts ih =>
    unfold termToConcrete at hrun
    simp only [bind, Except.bind, pure, Except.pure] at hrun
    split at hrun
    · cases hrun
    rename_i τ' _hτ
    split at hrun
    · cases hrun
    rename_i ts' hts'
    simp only [Except.ok.injEq] at hrun
    subst hrun
    refine .array ?_
    intro sub hsub
    exact Array.mem_mapM_ok_forall
      (P := fun x => x ∈ ts) (Q := Concrete.Term.RefsDt cd)
      (fun x hxMem fx hfx => ih x hxMem hfx) ts ts' (fun x hx => hx) hts' sub hsub
  | @ret typ e r _ ihr =>
    unfold termToConcrete at hrun
    simp only [bind, Except.bind, pure, Except.pure] at hrun
    split at hrun
    · cases hrun
    rename_i τ' _hτ
    split at hrun
    · cases hrun
    rename_i r' hr'
    simp only [Except.ok.injEq] at hrun
    subst hrun
    exact .ret (ihr hr')
  | @«let» typ e pat v b _hv _hb ihv ihb =>
    unfold termToConcrete at hrun
    simp only [bind, Except.bind, pure, Except.pure] at hrun
    split at hrun
    · cases hrun
    rename_i τ' _hτ
    split at hrun
    · cases hrun
    rename_i v' hv'
    split at hrun
    · cases hrun
    rename_i b' hb'
    -- The pattern match decides letVar vs letWild.
    cases pat with
    | var x =>
      simp only [Except.ok.injEq] at hrun
      subst hrun
      exact .letVar (ihv hv') (ihb hb')
    | wildcard =>
      simp only [Except.ok.injEq] at hrun
      subst hrun
      exact .letWild (ihv hv') (ihb hb')
    | field _ =>
      simp only [Except.ok.injEq] at hrun
      subst hrun
      exact .letWild (ihv hv') (ihb hb')
    | ref _ _ =>
      simp only [Except.ok.injEq] at hrun
      subst hrun
      exact .letWild (ihv hv') (ihb hb')
    | tuple _ =>
      simp only [Except.ok.injEq] at hrun
      subst hrun
      exact .letWild (ihv hv') (ihb hb')
    | array _ =>
      simp only [Except.ok.injEq] at hrun
      subst hrun
      exact .letWild (ihv hv') (ihb hb')
    | or _ _ =>
      simp only [Except.ok.injEq] at hrun
      subst hrun
      exact .letWild (ihv hv') (ihb hb')
    | pointer _ =>
      simp only [Except.ok.injEq] at hrun
      subst hrun
      exact .letWild (ihv hv') (ihb hb')
  | @«match» typ e scrut bs _hscrut _hcases ihscrut ihcases =>
    -- Delegated to the helper; passes the structural IHs for scrut and per-case bodies.
    exact termToConcrete_match_arm_preserves_RefsDt typ e scrut bs hwit
      (fun {cs} hcs => ihscrut hcs)
      (fun pc hpc {cb} hcb => ihcases pc hpc hcb)
      hrun
  | @app typ e g tArgs args u _hargs ih =>
    unfold termToConcrete at hrun
    simp only [bind, Except.bind, pure, Except.pure] at hrun
    split at hrun
    · cases hrun
    rename_i τ' _hτ
    split at hrun
    · cases hrun
    rename_i args' hargs'
    simp only [Except.ok.injEq] at hrun
    subst hrun
    refine .app ?_
    intro a ha
    exact List.mem_mapM_ok_forall
      (P := fun x => x ∈ args) (Q := Concrete.Term.RefsDt cd)
      (fun x hxMem fx hfx => ih x hxMem hfx) args args' (fun x hx => hx) hargs' a ha
  | @add typ e a b _ _ iha ihb =>
    unfold termToConcrete at hrun
    simp only [bind, Except.bind, pure, Except.pure] at hrun
    split at hrun
    · cases hrun
    rename_i τ' _hτ
    split at hrun
    · cases hrun
    rename_i a' ha'
    split at hrun
    · cases hrun
    rename_i b' hb'
    simp only [Except.ok.injEq] at hrun
    subst hrun
    exact .add (iha ha') (ihb hb')
  | @sub typ e a b _ _ iha ihb =>
    unfold termToConcrete at hrun
    simp only [bind, Except.bind, pure, Except.pure] at hrun
    split at hrun
    · cases hrun
    rename_i τ' _hτ
    split at hrun
    · cases hrun
    rename_i a' ha'
    split at hrun
    · cases hrun
    rename_i b' hb'
    simp only [Except.ok.injEq] at hrun
    subst hrun
    exact .sub (iha ha') (ihb hb')
  | @mul typ e a b _ _ iha ihb =>
    unfold termToConcrete at hrun
    simp only [bind, Except.bind, pure, Except.pure] at hrun
    split at hrun
    · cases hrun
    rename_i τ' _hτ
    split at hrun
    · cases hrun
    rename_i a' ha'
    split at hrun
    · cases hrun
    rename_i b' hb'
    simp only [Except.ok.injEq] at hrun
    subst hrun
    exact .mul (iha ha') (ihb hb')
  | @eqZero typ e a _ iha =>
    unfold termToConcrete at hrun
    simp only [bind, Except.bind, pure, Except.pure] at hrun
    split at hrun
    · cases hrun
    rename_i τ' _hτ
    split at hrun
    · cases hrun
    rename_i a' ha'
    simp only [Except.ok.injEq] at hrun
    subst hrun
    exact .eqZero (iha ha')
  | @proj typ e a n _ iha =>
    unfold termToConcrete at hrun
    simp only [bind, Except.bind, pure, Except.pure] at hrun
    split at hrun
    · cases hrun
    rename_i τ' _hτ
    split at hrun
    · cases hrun
    rename_i a' ha'
    simp only [Except.ok.injEq] at hrun
    subst hrun
    exact .proj (iha ha')
  | @get typ e a n _ iha =>
    unfold termToConcrete at hrun
    simp only [bind, Except.bind, pure, Except.pure] at hrun
    split at hrun
    · cases hrun
    rename_i τ' _hτ
    split at hrun
    · cases hrun
    rename_i a' ha'
    simp only [Except.ok.injEq] at hrun
    subst hrun
    exact .get (iha ha')
  | @slice typ e a i j _ iha =>
    unfold termToConcrete at hrun
    simp only [bind, Except.bind, pure, Except.pure] at hrun
    split at hrun
    · cases hrun
    rename_i τ' _hτ
    split at hrun
    · cases hrun
    rename_i a' ha'
    simp only [Except.ok.injEq] at hrun
    subst hrun
    exact .slice (iha ha')
  | @«set» typ e a n v _ _ iha ihv =>
    unfold termToConcrete at hrun
    simp only [bind, Except.bind, pure, Except.pure] at hrun
    split at hrun
    · cases hrun
    rename_i τ' _hτ
    split at hrun
    · cases hrun
    rename_i a' ha'
    split at hrun
    · cases hrun
    rename_i v' hv'
    simp only [Except.ok.injEq] at hrun
    subst hrun
    exact .set (iha ha') (ihv hv')
  | @store typ e a _ iha =>
    unfold termToConcrete at hrun
    simp only [bind, Except.bind, pure, Except.pure] at hrun
    split at hrun
    · cases hrun
    rename_i τ' _hτ
    split at hrun
    · cases hrun
    rename_i a' ha'
    simp only [Except.ok.injEq] at hrun
    subst hrun
    exact .store (iha ha')
  | @load typ e a _ iha =>
    unfold termToConcrete at hrun
    simp only [bind, Except.bind, pure, Except.pure] at hrun
    split at hrun
    · cases hrun
    rename_i τ' _hτ
    split at hrun
    · cases hrun
    rename_i a' ha'
    simp only [Except.ok.injEq] at hrun
    subst hrun
    exact .load (iha ha')
  | @ptrVal typ e a _ iha =>
    unfold termToConcrete at hrun
    simp only [bind, Except.bind, pure, Except.pure] at hrun
    split at hrun
    · cases hrun
    rename_i τ' _hτ
    split at hrun
    · cases hrun
    rename_i a' ha'
    simp only [Except.ok.injEq] at hrun
    subst hrun
    exact .ptrVal (iha ha')
  | @assertEq typ e a b r _ _ _ iha ihb ihr =>
    unfold termToConcrete at hrun
    simp only [bind, Except.bind, pure, Except.pure] at hrun
    split at hrun
    · cases hrun
    rename_i τ' _hτ
    split at hrun
    · cases hrun
    rename_i a' ha'
    split at hrun
    · cases hrun
    rename_i b' hb'
    split at hrun
    · cases hrun
    rename_i r' hr'
    simp only [Except.ok.injEq] at hrun
    subst hrun
    exact .assertEq (iha ha') (ihb hb') (ihr hr')
  | @ioGetInfo typ e k _ ihk =>
    unfold termToConcrete at hrun
    simp only [bind, Except.bind, pure, Except.pure] at hrun
    split at hrun
    · cases hrun
    rename_i τ' _hτ
    split at hrun
    · cases hrun
    rename_i k' hk'
    simp only [Except.ok.injEq] at hrun
    subst hrun
    exact .ioGetInfo (ihk hk')
  | @ioSetInfo typ e k i l r _ _ _ _ ihk ihi ihl ihr =>
    unfold termToConcrete at hrun
    simp only [bind, Except.bind, pure, Except.pure] at hrun
    split at hrun
    · cases hrun
    rename_i τ' _hτ
    split at hrun
    · cases hrun
    rename_i k' hk'
    split at hrun
    · cases hrun
    rename_i i' hi'
    split at hrun
    · cases hrun
    rename_i l' hl'
    split at hrun
    · cases hrun
    rename_i r' hr'
    simp only [Except.ok.injEq] at hrun
    subst hrun
    exact .ioSetInfo (ihk hk') (ihi hi') (ihl hl') (ihr hr')
  | @ioRead typ e i n _ ihi =>
    unfold termToConcrete at hrun
    simp only [bind, Except.bind, pure, Except.pure] at hrun
    split at hrun
    · cases hrun
    rename_i τ' _hτ
    split at hrun
    · cases hrun
    rename_i i' hi'
    simp only [Except.ok.injEq] at hrun
    subst hrun
    exact .ioRead (ihi hi')
  | @ioWrite typ e d r _ _ ihd ihr =>
    unfold termToConcrete at hrun
    simp only [bind, Except.bind, pure, Except.pure] at hrun
    split at hrun
    · cases hrun
    rename_i τ' _hτ
    split at hrun
    · cases hrun
    rename_i d' hd'
    split at hrun
    · cases hrun
    rename_i r' hr'
    simp only [Except.ok.injEq] at hrun
    subst hrun
    exact .ioWrite (ihd hd') (ihr hr')
  | @u8BitDecomposition typ e a _ iha =>
    unfold termToConcrete at hrun
    simp only [bind, Except.bind, pure, Except.pure] at hrun
    split at hrun
    · cases hrun
    rename_i τ' _hτ
    split at hrun
    · cases hrun
    rename_i a' ha'
    simp only [Except.ok.injEq] at hrun
    subst hrun
    exact .u8BitDecomposition (iha ha')
  | @u8ShiftLeft typ e a _ iha =>
    unfold termToConcrete at hrun
    simp only [bind, Except.bind, pure, Except.pure] at hrun
    split at hrun
    · cases hrun
    rename_i τ' _hτ
    split at hrun
    · cases hrun
    rename_i a' ha'
    simp only [Except.ok.injEq] at hrun
    subst hrun
    exact .u8ShiftLeft (iha ha')
  | @u8ShiftRight typ e a _ iha =>
    unfold termToConcrete at hrun
    simp only [bind, Except.bind, pure, Except.pure] at hrun
    split at hrun
    · cases hrun
    rename_i τ' _hτ
    split at hrun
    · cases hrun
    rename_i a' ha'
    simp only [Except.ok.injEq] at hrun
    subst hrun
    exact .u8ShiftRight (iha ha')
  | @u8Xor typ e a b _ _ iha ihb =>
    unfold termToConcrete at hrun
    simp only [bind, Except.bind, pure, Except.pure] at hrun
    split at hrun
    · cases hrun
    rename_i τ' _hτ
    split at hrun
    · cases hrun
    rename_i a' ha'
    split at hrun
    · cases hrun
    rename_i b' hb'
    simp only [Except.ok.injEq] at hrun
    subst hrun
    exact .u8Xor (iha ha') (ihb hb')
  | @u8Add typ e a b _ _ iha ihb =>
    unfold termToConcrete at hrun
    simp only [bind, Except.bind, pure, Except.pure] at hrun
    split at hrun
    · cases hrun
    rename_i τ' _hτ
    split at hrun
    · cases hrun
    rename_i a' ha'
    split at hrun
    · cases hrun
    rename_i b' hb'
    simp only [Except.ok.injEq] at hrun
    subst hrun
    exact .u8Add (iha ha') (ihb hb')
  | @u8Sub typ e a b _ _ iha ihb =>
    unfold termToConcrete at hrun
    simp only [bind, Except.bind, pure, Except.pure] at hrun
    split at hrun
    · cases hrun
    rename_i τ' _hτ
    split at hrun
    · cases hrun
    rename_i a' ha'
    split at hrun
    · cases hrun
    rename_i b' hb'
    simp only [Except.ok.injEq] at hrun
    subst hrun
    exact .u8Sub (iha ha') (ihb hb')
  | @u8And typ e a b _ _ iha ihb =>
    unfold termToConcrete at hrun
    simp only [bind, Except.bind, pure, Except.pure] at hrun
    split at hrun
    · cases hrun
    rename_i τ' _hτ
    split at hrun
    · cases hrun
    rename_i a' ha'
    split at hrun
    · cases hrun
    rename_i b' hb'
    simp only [Except.ok.injEq] at hrun
    subst hrun
    exact .u8And (iha ha') (ihb hb')
  | @u8Or typ e a b _ _ iha ihb =>
    unfold termToConcrete at hrun
    simp only [bind, Except.bind, pure, Except.pure] at hrun
    split at hrun
    · cases hrun
    rename_i τ' _hτ
    split at hrun
    · cases hrun
    rename_i a' ha'
    split at hrun
    · cases hrun
    rename_i b' hb'
    simp only [Except.ok.injEq] at hrun
    subst hrun
    exact .u8Or (iha ha') (ihb hb')
  | @u8LessThan typ e a b _ _ iha ihb =>
    unfold termToConcrete at hrun
    simp only [bind, Except.bind, pure, Except.pure] at hrun
    split at hrun
    · cases hrun
    rename_i τ' _hτ
    split at hrun
    · cases hrun
    rename_i a' ha'
    split at hrun
    · cases hrun
    rename_i b' hb'
    simp only [Except.ok.injEq] at hrun
    subst hrun
    exact .u8LessThan (iha ha') (ihb hb')
  | @u32LessThan typ e a b _ _ iha ihb =>
    unfold termToConcrete at hrun
    simp only [bind, Except.bind, pure, Except.pure] at hrun
    split at hrun
    · cases hrun
    rename_i τ' _hτ
    split at hrun
    · cases hrun
    rename_i a' ha'
    split at hrun
    · cases hrun
    rename_i b' hb'
    simp only [Except.ok.injEq] at hrun
    subst hrun
    exact .u32LessThan (iha ha') (ihb hb')
  | @debug typ e label tOpt r ht hr iht ihr =>
    -- Case-split tOpt UP FRONT so termToConcrete unfolds cleanly.
    cases htmatch : tOpt with
    | none =>
      rw [htmatch] at hrun
      unfold termToConcrete at hrun
      simp only [bind, Except.bind, pure, Except.pure] at hrun
      -- t' = none branch (no inner match needed since we go directly to pure none)
      split at hrun
      · cases hrun
      rename_i τ' _hτ
      split at hrun
      · cases hrun
      rename_i r' hr'
      simp only [Except.ok.injEq] at hrun
      subst hrun
      refine .debug ?_ (ihr hr')
      intro tval htval; cases htval
    | some sub =>
      rw [htmatch] at hrun
      unfold termToConcrete at hrun
      simp only [bind, Except.bind, pure, Except.pure] at hrun
      split at hrun
      · cases hrun
      rename_i sub' hsub'
      split at hrun
      · cases hrun
      rename_i τ' _hτ
      split at hrun
      · cases hrun
      rename_i r' hr'
      simp only [Except.ok.injEq] at hrun
      subst hrun
      refine .debug ?_ (ihr hr')
      intro tval htval
      -- htval : some sub' = some tval (after simp), htmatch : tOpt = some sub
      simp only [Option.some.injEq] at htval
      subst htval
      exact iht sub htmatch hsub'

/-- Drain-state invariant: every newly-emitted function body satisfies
`Typed.Term.RefsDt tds`. Mirrors `NewFunctionsFO`. -/
private def DrainState.NewFunctionsTermRefsDt
    (tds : Typed.Decls) (st : DrainState) : Prop :=
  ∀ f ∈ st.newFunctions, Typed.Term.RefsDt tds f.body

private theorem DrainState.NewFunctionsTermRefsDt.init
    {tds : Typed.Decls}
    (pending : Std.HashSet (Global × Array Typ)) :
    DrainState.NewFunctionsTermRefsDt tds
      { pending, seen := {}, mono := {}, newFunctions := #[], newDataTypes := #[] } := by
  intro f hf
  simp only [Array.not_mem_empty] at hf

/-- Step preservation: `concretizeDrainEntry` keeps `NewFunctionsTermRefsDt`.
For the function-arm case, it pushes a new function whose body is
`substInTypedTerm subst f.body`. The `Typed.Term.RefsDt tds` predicate
must transport across `substInTypedTerm`; under `params = []` this is the
empty substitution, identity. -/
private theorem concretizeDrainEntry_preserves_NewFunctionsTermRefsDt
    {decls : Typed.Decls} (hP : Typed.Decls.TermRefsDt decls)
    (hparamsEmpty : ∀ g f, decls.getByKey g = some (.function f) → f.params = [])
    {state state' : DrainState}
    (hinv : DrainState.NewFunctionsTermRefsDt decls state) (entry : Global × Array Typ)
    (hstep : concretizeDrainEntry decls state entry = .ok state') :
    DrainState.NewFunctionsTermRefsDt decls state' := by
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
        intro f' hf'mem
        rcases Array.mem_push.mp hf'mem with hin | heq
        · exact hinv f' hin
        · subst heq
          simp only
          -- Body is `substInTypedTerm subst f.body` where `subst = mkParamSubst f.params args`.
          -- Under `params = []`, `mkParamSubst [] _ _ = none`, so `substInTypedTerm`
          -- collapses to identity on `f.body`. Then `Typed.Term.RefsDt decls f.body`
          -- carries from `hP` directly.
          have hpe : f.params = [] := hparamsEmpty entry.1 f hf_get
          have hbody_id : substInTypedTerm (mkParamSubst f.params entry.2) f.body = f.body := by
            rw [hpe, mkParamSubst_nil]
            exact substInTypedTerm_empty_id f.body
          rw [hbody_id]
          exact hP entry.1 f hf_get
      · exact absurd hstep (by intro h; cases h)
    · rename_i dt hdt_get
      split at hstep
      · simp only [Except.ok.injEq] at hstep
        rw [← hstep]
        intro f hf; exact hinv f hf
      · exact absurd hstep (by intro h; cases h)
    · cases hstep

private theorem concretizeDrainEntry_list_foldlM_preserves_NewFunctionsTermRefsDt
    {decls : Typed.Decls} (hP : Typed.Decls.TermRefsDt decls)
    (hparamsEmpty : ∀ g f, decls.getByKey g = some (.function f) → f.params = [])
    (L : List (Global × Array Typ))
    (state0 state' : DrainState)
    (hinv0 : DrainState.NewFunctionsTermRefsDt decls state0)
    (hstep : L.foldlM (concretizeDrainEntry decls) state0 = .ok state') :
    DrainState.NewFunctionsTermRefsDt decls state' := by
  induction L generalizing state0 with
  | nil =>
    simp only [List.foldlM, pure, Except.pure, Except.ok.injEq] at hstep
    rw [← hstep]; exact hinv0
  | cons hd tl ih =>
    simp only [List.foldlM, bind, Except.bind] at hstep
    split at hstep
    · cases hstep
    · rename_i s'' hs''
      have hinv1 : DrainState.NewFunctionsTermRefsDt decls s'' :=
        concretizeDrainEntry_preserves_NewFunctionsTermRefsDt hP hparamsEmpty hinv0 hd hs''
      exact ih s'' hinv1 hstep

private theorem concretizeDrainIter_preserves_NewFunctionsTermRefsDt
    {decls : Typed.Decls} (hP : Typed.Decls.TermRefsDt decls)
    (hparamsEmpty : ∀ g f, decls.getByKey g = some (.function f) → f.params = [])
    {state state' : DrainState}
    (hinv : DrainState.NewFunctionsTermRefsDt decls state)
    (hstep : concretizeDrainIter decls state = .ok state') :
    DrainState.NewFunctionsTermRefsDt decls state' := by
  unfold concretizeDrainIter at hstep
  rw [← Array.foldlM_toList] at hstep
  let state0 : DrainState := { state with pending := ∅ }
  have hinv0 : DrainState.NewFunctionsTermRefsDt decls state0 := hinv
  exact concretizeDrainEntry_list_foldlM_preserves_NewFunctionsTermRefsDt hP hparamsEmpty
    state.pending.toArray.toList state0 state' hinv0 hstep

private theorem concretize_drain_preserves_NewFunctionsTermRefsDt
    {decls : Typed.Decls} (hP : Typed.Decls.TermRefsDt decls)
    (hparamsEmpty : ∀ g f, decls.getByKey g = some (.function f) → f.params = [])
    (fuel : Nat) (init : DrainState)
    (hinv : DrainState.NewFunctionsTermRefsDt decls init)
    {drained : DrainState}
    (hdrain : concretizeDrain decls fuel init = .ok drained) :
    DrainState.NewFunctionsTermRefsDt decls drained := by
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
        have hinv' : DrainState.NewFunctionsTermRefsDt decls state' :=
          concretizeDrainIter_preserves_NewFunctionsTermRefsDt hP hparamsEmpty hinv hstate'
        exact ih state' hinv' hdrain

/-! #### `concretizeBuild` typed-side `TermRefsDt` preservation. -/

/-- `concretizeBuild` produces a typed-side `TermRefsDt` over the resulting
`monoDecls`. Each function body is `rewriteTypedTerm` of either the source
body or a drained `newFunctions[i].body`. The structural lemma
`rewriteTypedTerm_preserves_RefsDt` (F=0 above) discharges the per-body case
once we supply the dt/ctor bridges (`hdt_bridge`, `hctor_bridge`,
`hrewriteGlobal_preserve`).

Sorried as a single composition target — the bridges require tracking
how `concretizeBuild`'s 3-fold inserts dt/ctor keys: source dt/ctor keys
survive into `monoDecls` via `fromSource`; drained dt-keys (from
`newDataTypes`) appear in `monoDecls` via `withNewDts`, paired with
constructor inserts under `dt.name.pushNamespace c.nameHead`. Combined
with `rewriteGlobal`'s case analysis (function-typed g + mono-hit →
function-keyed in monoDecls; constructor-typed g + mono-hit → ctor-keyed
in monoDecls), the bridges close. -/
private theorem concretizeBuild_preserves_TermRefsDt
    {typedDecls : Typed.Decls} {mono : MonoMap}
    {newFunctions : Array Typed.Function} {newDataTypes : Array DataType}
    (_htdsRef : Typed.Decls.TermRefsDt typedDecls)
    (_hnfRef : ∀ f ∈ newFunctions, Typed.Term.RefsDt typedDecls f.body) :
    Typed.Decls.TermRefsDt
      (concretizeBuild typedDecls mono newFunctions newDataTypes) := by
  -- BLOCKED ON: 3-fold preservation chain via `rewriteTypedTerm_preserves_RefsDt`
  -- (closed F=0 above). Each fold (fromSource / withNewDts / newFunctions)
  -- preserves a `TermRefsDt`-style invariant; final result is the chain
  -- composition.
  --
  -- Granular sub-targets (each F=1, mechanical 30-50 LoC):
  --
  -- (1.A) newFunctions-fold function-origin inversion: for the resulting
  --       `.function f` at key g, either pre-existing in input acc, OR `f.body
  --       = rewriteTypedTerm typedDecls _ mono nf.body` for some
  --       `nf ∈ newFunctions`. Mechanical Array.foldl_induction.
  --
  -- (1.B) withNewDts-fold function preservation: function-keyed entries are
  --       unaffected by the newDataTypes fold (only inserts dt/ctor entries).
  --       Mechanical foldl_induction.
  --
  -- (1.C) fromSource-fold function-origin inversion: the resulting `.function f`
  --       at key g originates from a typedDecls-keyed `.function f₀` with
  --       `f.body = rewriteTypedTerm typedDecls _ mono f₀.body`. Mechanical.
  --
  -- (2)   dt/ctor key bridge: typedDecls dt/ctor witnesses survive insert-only
  --       3-fold composition into the final concretizeBuild output.
  --       Mechanical monotonicity.
  --
  -- (3)   rewriteGlobal_preserve: under a typedDecls-keyed dt/ctor witness on
  --       g, `rewriteGlobal typedDecls mono g tArgs` yields a typedDecls-keyed
  --       dt/ctor result. Case-split on the rewriteGlobal definition; the
  --       constructor case requires a WellFormed-source hypothesis that
  --       `mono[(dt.name, tArgs)]` lands at a typedDecls dt-key.
  --       BLOCKED on the latter: `mono` is a private DrainState field, and
  --       its targets only become typedDecls-keyed after concretizeBuild
  --       inserts them — circular without strengthening the calling-site
  --       hypotheses.
  --
  -- Composition (F=0 once 1.A/1.B/1.C/2/3 are F=0):
  --   intro g f hget
  --   unfold concretizeBuild at hget
  --   rcases newFunctions_fold_origin hget with hpre | ⟨nf, hnf_mem, hbody⟩
  --   case (1):  apply withNewDts_preserves_function on hpre, then
  --              fromSource_origin to obtain f₀ with hf_body_eq + hf₀_RefsDt
  --              from htdsRef. Apply rewriteTypedTerm_preserves_RefsDt with
  --              dt_witness_bridge + rewriteGlobal_preserve.
  --   case (2):  hnfRef applied directly to nf. Same closing application.
  --
  -- Total ~150-200 LoC across the 5 sub-helpers + 30 LoC composition.
  sorry

/-! #### `step4Lower` fold: typed-side → concrete-side `TermRefsDt`.

Each typed function body becomes its `termToConcrete` lowering. We need
`Concrete.Term.RefsDt cd (termToConcrete _ body)` from
`Typed.Term.RefsDt monoDecls body`, using bridges between dt/ctor keys
across the lowering step. Crucially, `step4Lower`'s function/dataType/
constructor arms preserve dt/ctor key-witnesses bijectively. -/

/-- Function-key inversion for the `step4Lower` fold: every `.function cf`
entry in the post-fold `concDecls` originates from a `.function f` entry in
`monoDecls` at the same key, with `cf.body = (termToConcrete emptyMono f.body)`.

Replay of `step4Lower_fold_kind_at_key`'s split strategy specialised to the
function arm. -/
private theorem step4Lower_fold_function_origin
    {monoDecls : Typed.Decls} {concDecls : Concrete.Decls}
    {g : Global} {cf : Concrete.Function}
    (hcf_get : concDecls.getByKey g = some (.function cf))
    (hfold : monoDecls.foldlM (init := default) step4Lower = .ok concDecls) :
    ∃ f : Typed.Function,
      monoDecls.getByKey g = some (.function f) ∧
      termToConcrete (∅ : Std.HashMap (Global × Array Typ) Global) f.body = .ok cf.body := by
  -- Define a fold-level invariant on Concrete.Decls states:
  -- `P acc := every .function entry in acc has body = termToConcrete _ f.body
  --   for some f keyed identically in monoDecls`.
  let P : Concrete.Decls → Prop := fun acc =>
    ∀ g' cf', acc.getByKey g' = some (.function cf') →
      ∃ f' : Typed.Function,
        monoDecls.getByKey g' = some (.function f') ∧
        termToConcrete (∅ : Std.HashMap (Global × Array Typ) Global) f'.body = .ok cf'.body
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
      -- step4Lower on .function f: inserts `.function cf_step` at name where
      -- cf_step.body = termToConcrete _ f.body.
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
      by_cases hkn : (name == g') = true
      · have hkEq : name = g' := LawfulBEq.eq_of_beq hkn
        subst hkEq
        rw [IndexMap.getByKey_insert_self] at hget
        simp only [Option.some.injEq, Concrete.Declaration.function.injEq] at hget
        subst hget
        refine ⟨f, ?_, ?_⟩
        · exact IndexMap.getByKey_of_mem_pairs _ _ _ hxmem
        · exact hBody
      · have hne : (name == g') = false := Bool.not_eq_true _ |>.mp hkn
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

-- `step4Lower_fold_preserves_TermRefsDt` and `concretize_preserves_TermRefsDt`
-- are defined further below, AFTER the dt/ctor bridges, which themselves are
-- defined AFTER `indexMap_pairs_key_unique` (so they can use it directly).

/-! ### Phase 3 — `typFlatSize` preservation across concretize (main theorem). -/

-- `Typ.typFlatSize_across_concretize` DELETED: FALSE as stated. `rewriteTyp`
-- maps `.app g args → .ref concName` when mono has an entry, but
-- `typFlatSize decls {} (.ref concName) ≠ typFlatSize decls {} (.app g args)
-- = typFlatSize decls {} (.ref g)` in general (concName looks up a different
-- datatype in decls, if it's even a key). Needs either a two-decls
-- formulation (RHS evaluated in `monoDecls` where concName resolves) or a
-- restrictive hypothesis ("top-level input types are `.app`-free"). Orphan
-- at deletion time — no caller. Reintroduce with a correct signature when a
-- concrete consumer needs it.

/-! ## Concretize stage extraction

These lemmas expose internals of `Typed.Decls.concretize`'s do-block so
downstream proofs (`CompilerPreservation.concretize_keys_of_mono`) can access
specific stage outputs. Sorried until `concretize`'s imperative body is
refactored into extractable form. -/

/-- Step 4 of `Typed.Decls.concretize` is key-preserving: any insert-only step
function `lower` that inserts under `.fst` gives `monoDecls`-keys ↔ `concDecls`-keys. -/
theorem concretize_step_4_keys_of_fold
    {monoDecls : Typed.Decls} {concDecls : Concrete.Decls}
    (lower : Concrete.Decls → Global × Typed.Declaration →
             Except ConcretizeError Concrete.Decls)
    (hlower_insert : ∀ acc x r, lower acc x = .ok r →
      ∀ g, r.containsKey g ↔ acc.containsKey g ∨ (x.fst == g) = true)
    (hfold : monoDecls.foldlM (init := default) lower = .ok concDecls) :
    ∀ g, monoDecls.containsKey g ↔ concDecls.containsKey g := by
  intro g
  rw [IndexMap.containsKey_iff_exists_pair monoDecls g,
      ← IndexMap.indexMap_foldlM_insertKey_default_iff monoDecls lower hlower_insert g
        concDecls hfold]

/-- `step4Lower` is insert-only in its input's `.fst`. -/
theorem step4Lower_inserts :
    ∀ acc x r, step4Lower acc x = .ok r →
      ∀ g, r.containsKey g ↔ acc.containsKey g ∨ (x.fst == g) = true := by
  intro acc x r hstep g
  obtain ⟨name, d⟩ := x
  unfold step4Lower at hstep
  simp only at hstep
  cases d with
  | function f =>
    simp only [bind, Except.bind, pure, Except.pure] at hstep
    split at hstep
    · contradiction
    split at hstep
    · contradiction
    split at hstep
    · contradiction
    simp only [Except.ok.injEq] at hstep
    subst hstep
    exact IndexMap.containsKey_insert_iff_or acc name g _
  | dataType dt =>
    simp only [bind, Except.bind, pure, Except.pure] at hstep
    split at hstep
    · contradiction
    simp only [Except.ok.injEq] at hstep
    subst hstep
    exact IndexMap.containsKey_insert_iff_or acc name g _
  | constructor dt c =>
    simp only [bind, Except.bind, pure, Except.pure] at hstep
    split at hstep
    · contradiction
    split at hstep
    · contradiction
    simp only [Except.ok.injEq] at hstep
    subst hstep
    exact IndexMap.containsKey_insert_iff_or acc name g _

/-- Existence of the `monoDecls` witness for `step4Lower`'s fold. Closed by
unfolding `Typed.Decls.concretize` — its final action is
`monoDecls.foldlM (init := default) step4Lower` for `monoDecls = concretizeBuild …`. -/
theorem step4_monoDecls_exists
    {typedDecls : Typed.Decls} {concDecls : Concrete.Decls}
    (hconc : typedDecls.concretize = .ok concDecls) :
    ∃ (monoDecls : Typed.Decls),
      monoDecls.foldlM (init := default) step4Lower = .ok concDecls := by
  unfold Typed.Decls.concretize at hconc
  simp only [bind, Except.bind] at hconc
  split at hconc
  · contradiction
  · rename_i drained hdrain
    exact ⟨concretizeBuild typedDecls drained.mono drained.newFunctions drained.newDataTypes,
           hconc⟩

/-- Step 4 `foldlM` extraction: composed from `step4_monoDecls_exists` +
`step4Lower_inserts`. -/
theorem concretize_step_4_extract
    {typedDecls : Typed.Decls} {concDecls : Concrete.Decls}
    (_hconc : typedDecls.concretize = .ok concDecls) :
    ∃ (monoDecls : Typed.Decls)
      (lower : Concrete.Decls → Global × Typed.Declaration →
               Except ConcretizeError Concrete.Decls),
      (∀ acc x r, lower acc x = .ok r →
        ∀ g, r.containsKey g ↔ acc.containsKey g ∨ (x.fst == g) = true) ∧
      monoDecls.foldlM (init := default) lower = .ok concDecls := by
  obtain ⟨monoDecls, hfold⟩ := step4_monoDecls_exists _hconc
  exact ⟨monoDecls, step4Lower, step4Lower_inserts, hfold⟩

/-! ### Sub-lemmas for `concretize_preserves_runFunction`

The concretize preservation theorem decomposes into (A) `Typ.instantiate` /
`substInTypedTerm` are value-level identity, (B) `rewriteTypedTerm` preserves
`Source.Eval` denotation
modulo funcIdx remap, (C) 40-arm structural induction on `Typed.Term`.

These stubs name the pieces so future work can attack them individually. -/

/-! **Placeholder obligations (A) and (B)**: value-level denotation is
preserved by `substInTypedTerm` / `rewriteTypedTerm` respectively. Both
operate on `Typed.Term` while `Source.Eval.interp` operates on `Source.Term`,
so the precise statements require either (a) a `Typed.interp` evaluator
mirroring `Source.Eval.interp` and a compilation bridge, or (b) a
`decls`-modification construct (`decls[name.body := rewrite name.body]`)
that threads the rewrite through the source evaluator.

Both route to the heart theorem `concretize_preserves_runFunction`
(below). Stating them precisely is itself concretize-preservation groundwork
— see the `concretize_preserves_runFunction` per-arm plan for the proper
framing (37-arm induction quotients out the rename). **These stubs are
intentionally *not* stated as theorems**: expressing them requires
infrastructure that isn't in place. They live here only as documentation
anchors for future `BLOCKED ON:` references. -/

/-- Bridge: `funcIdx` maps source globals and their concretized images to the
same slot. Required so `flattenValue` of `.fn g` and `.fn (concretizeName g args)`
agree. Discharged by the top-level caller via `ct.nameMap` composition with the mono-map. -/
@[expose]
def FuncIdxRespectsConcretize
    (mono : Std.HashMap (Global × Array Typ) Global)
    (funcIdx : Global → Option Nat) : Prop :=
  ∀ (g : Global) (args : Array Typ) (g' : Global),
    mono[(g, args)]? = some g' → funcIdx g = funcIdx g'

/-- Bridge: `decls : Source.Decls` and `typedDecls : Typed.Decls` share
declaration skeleton — every source name resolves in both. Typically
discharged from `checkAndSimplify = .ok typedDecls`. -/
@[expose]
def SourceTypedCompatible
    (decls : Source.Decls) (typedDecls : Typed.Decls) : Prop :=
  ∀ name, decls.getByKey name = none ↔ typedDecls.getByKey name = none

-- `ValueRelByConcretize` + `flattenValue_of_ValueRel` DELETED: speculative
-- infrastructure for a possible future upgraded signature of
-- `concretize_preserves_runFunction`. Current signature uses
-- `Concrete.flattenValue concDecls` on the RHS and bridges to source
-- `flattenValue decls` via `flatten_agree_under_fullymono` for composition
-- with the bytecode chain.

/-- Bridge: under `FullyMonomorphic t` (which forces every datatype/function
parameter list to be empty, hence `concretizeName g #[] = g` for all globals),
source-decls `flattenValue` and concrete-decls `Concrete.flattenValue` agree
pointwise on every value. Required to compose
`concretize_preserves_runFunction`'s new RHS form
(`Concrete.flattenValue concDecls`) back into the bytecode chain (which uses
`flattenValue decls` everywhere through `InterpResultEq`).

Proof obligation: under FullyMono + `mkDecls = .ok decls` +
`checkAndSimplify = .ok typedDecls` + `concretize = .ok concDecls`:
- For every ctor name `g`, `decls.getByKey g = some (.constructor dt₁ ctor₁)`
  iff `concDecls.getByKey g = some (.constructor dt₂ ctor₂)` with corresponding
  `dt`/`ctor` shapes (the `nameHead` agreement and ctor-arg-list shape).
- `dataTypeFlatSize` agrees on the corresponding `dt`s (constructors' arg-types
  rewrite to concretized variants but preserve flat size under FullyMono since
  args are empty).

Discharged via the per-decl reflection lemmas in CheckSound + the
`concretizeName g #[] = g` lemma (`concretizeName_empty_args`) under
FullyMono. -/
-- Pointwise flatMap helper. -/
private theorem flatten_attach_flatMap_eq_pw {vs : Array Value}
    {g₁ g₂ : Value → Array G}
    (h : ∀ v ∈ vs, g₁ v = g₂ v) :
    vs.attach.flatMap (fun ⟨v, _⟩ => g₁ v) =
    vs.attach.flatMap (fun ⟨v, _⟩ => g₂ v) := by
  congr 1
  funext ⟨v, hv⟩
  exact h v hv

/-! ### PLAN_3B Phase A.1 — source↔typed ctor kind correspondence (forward).

Given source `(.constructor dt c)` at key g, typed `(.constructor _ _)` at the
same key g. Derived from `FnMatchP_checkAndSimplify` (typed→source) by case-
analysis on what `tds.getByKey g` could be: rule out `none`/`.function`/
`.dataType` via key-set preservation + FnMatchP backward direction. -/
theorem checkAndSimplify_preserves_ctor_kind_fwd
    {t : Source.Toplevel} {decls : Source.Decls} {typedDecls : Typed.Decls}
    (hdecls : t.mkDecls = .ok decls)
    (hts : t.checkAndSimplify = .ok typedDecls)
    {g : Global} {dt : DataType} {c : Constructor}
    (hsrc : decls.getByKey g = some (.constructor dt c)) :
    ∃ td_dt td_c, typedDecls.getByKey g = some (.constructor td_dt td_c) := by
  have hkeys := checkAndSimplify_keys_local hdecls hts g
  have hsrc_ne : decls.getByKey g ≠ none := by rw [hsrc]; simp
  have htd_ne : typedDecls.getByKey g ≠ none := hkeys.mp hsrc_ne
  have hP := FnMatchP_checkAndSimplify hdecls hts
  match htd : typedDecls.getByKey g with
  | none => exact absurd htd htd_ne
  | some (.function tf) =>
    exfalso
    obtain ⟨_, hfsrc, _⟩ := (hP g).1 tf htd
    rw [hsrc] at hfsrc; cases hfsrc
  | some (.dataType dt') =>
    exfalso
    have := (hP g).2.1 dt' htd
    rw [hsrc] at this; cases this
  | some (.constructor td_dt td_c) =>
    exact ⟨td_dt, td_c, rfl⟩

-- `flatten_agree_under_fullymono` + Phase B/C sub-sorries placed after Phase A.4
-- below (they all need the Phase A.4 lemma which is defined post-`PhaseA2`).

/-- Aux lemma: the monomorphized decl table reproduces source-level
`runFunction` results up to `flattenValue` and `IOBuffer.equiv`.
Heart of the concretize-preservation proof — 37-arm induction over `Typed.Term`.

BLOCKED ON: 37 per-arm sub-lemmas (one per `Typed.Term` constructor), each
dispatched on the function body's outermost shape via a `HeartBodyShape`-style
predicate. Summary of per-arm strategy:

- **Leaves (4)**: `unit`, `var`, `ref`, `field` — direct unfold; `ref` cites
  funcIdx-compatibility + `Typ.typFlatSize_rewriteTyp_eq` (with the
  `MonoCompatible` hypothesis now available).
- **Structural (2)**: `tuple`, `array` — per-element IH under `evalList`.
- **Binders (3)**: `ret` (1 IH), `letT` (pattern binding + 2 IHs, cites
  `substInTypedTerm_preserves_source_eval`), `matchT` (case-list +
  `ConcretizeReady`).
- **Call (1)**: `app` — cites `rewriteTypedTerm_preserves_source_eval`
  + fuel-decrement + arg-list IH.
- **Arithmetic (4)**: `add`, `sub`, `mul`, `eqZero`.
- **Aggregate access (4)**: `proj`, `get`, `slice`, `set`.
- **Heap (3)**: `store`, `load`, `ptrVal` (IOBuffer heap equivalence).
- **Assert (1)**: `assertEq`.
- **IO (4)**: `ioGetInfo`, `ioSetInfo`, `ioRead`, `ioWrite`.
- **u8 ops (9)**: `u8BitDecomposition`, `u8ShiftLeft`, `u8ShiftRight`,
  `u8Xor`, `u8Add`, `u8Sub`, `u8And`, `u8Or`, `u8LessThan`.
- **u32 (1)**: `u32LessThan` (reuses `.tuple` IH over 4 bytes).
- **Debug (1)**: `debug` — transparent passthrough.

Plus a driver doing `cases` on `typedDecls.getByKey name`'s body shape and
dispatching to the appropriate arm. -/
private theorem concretize_preserves_runFunction
    {t : Source.Toplevel} {decls : Source.Decls} {typedDecls : Typed.Decls}
    {concDecls : Concrete.Decls}
    -- Sig strengthened (2026-04-24, SORRY_AUDIT_AGENT1.md §2): original sig
    -- with only `SourceTypedCompatible` is FALSE-as-stated — compares
    -- source/typed not source/concrete, misses ctor-rename, source-kind/
    -- concrete-kind mismatches. `FullyMonomorphic` + `mkDecls` / `checkAndSimplify`
    -- witnesses rule out polymorphic specialization (no ctor rename under
    -- `concretizeName g #[] = g`). RHS migrated (2026-04-24, second pass) to
    -- `Concrete.flattenValue concDecls` since post-concretize values carry
    -- mangled ctor names not in `decls` — flattening them via source `decls`
    -- is FALSE for any program where ctors are concretized differently from
    -- their source names.
    (_hmono : FullyMonomorphic t)
    (_hdecls : t.mkDecls = .ok decls)
    (_hts : t.checkAndSimplify = .ok typedDecls)
    (_hconc : typedDecls.concretize = .ok concDecls)
    (_hcompat : SourceTypedCompatible decls typedDecls)
    (name : Global)
    (_hnameSrc : decls.getByKey name ≠ none)
    (_hnameConc : concDecls.getByKey name ≠ none)
    (args : List Value) (io₀ : IOBuffer) (fuel : Nat)
    (funcIdx : Global → Option Nat)
    (mono : Std.HashMap (Global × Array Typ) Global)
    (_hidx : FuncIdxRespectsConcretize mono funcIdx) :
    -- LHS uses source `flattenValue decls` (source values resolve in source
    -- decls); RHS uses `Concrete.flattenValue concDecls` (concrete values
    -- carry mangled ctor names that resolve only in concDecls). Composition
    -- with the bytecode chain (which uses `flattenValue decls` everywhere)
    -- requires a bridge under FullyMono — see `flatten_agree_under_fullymono`.
    match Source.Eval.runFunction decls name args io₀ fuel,
          Concrete.Eval.runFunction concDecls name args io₀ fuel with
    | .ok (v₁, io₁), .ok (v₂, io₂) =>
        flattenValue decls funcIdx v₁ = Concrete.flattenValue concDecls funcIdx v₂
          ∧ IOBuffer.equiv io₁ io₂
    | .error _, .error _ => True
    | _, _ => False := by
  sorry

/-- Preservation: concretize preserves observable denotation, at both the
value level (modulo `concretizeName` renaming of globals inside `.fn`/`.ctor`,
captured by `funcIdx`) and the IOBuffer level.

Signature upgraded from a pure IOBuffer projection to a full
`(flattenValue-eq ∧ IOBuffer-equiv)` two-conjunct form so that top-level
composition can cite it against `InterpResultEq`. The caller supplies a
shared `funcIdx : Global → Option Nat` that resolves both original names
(as they appear in `v₁ : Source.Value`) and monomorphized names (as they
appear in `v₂ : Concrete.Value`) — top-level preservation constructs this from
`CompiledToplevel.nameMap` composed with the `concretizeName` mapping.

The proof will proceed by induction on the typed-term structure, using that
`Value` is type-erased (so substitution-through-types is semantically the
identity on values) and that `concretizeName` is injective.

-- BLOCKED ON: full concretize preservation proof — 40-arm structural
-- induction over `Typed.Term` + rewrite lemma `Typ.instantiate` /
-- `rewriteTypedTerm` preserve Source.Eval denotation. Not in session scope. -/
theorem Typed.Decls.concretize_preservation
    {t : Source.Toplevel} {decls : Source.Decls}
    {typedDecls : Typed.Decls} {concDecls : Concrete.Decls}
    (hmono : FullyMonomorphic t)
    (hdecls : t.mkDecls = .ok decls)
    (hts : t.checkAndSimplify = .ok typedDecls)
    (hconc : typedDecls.concretize = .ok concDecls)
    (hcompat : SourceTypedCompatible decls typedDecls) :
    ∀ (name : Global)
      -- `name` must appear in **both** `decls` and `concDecls` — shared
      -- across the name spaces (scopes the claim to first-order monomorphic
      -- functions present in both source and concretize output).
      (_hnameSrc : decls.getByKey name ≠ none)
      (_hnameConc : concDecls.getByKey name ≠ none)
      (args : List Value) (io₀ : IOBuffer) (fuel : Nat)
      (funcIdx : Global → Option Nat)
      (mono : Std.HashMap (Global × Array Typ) Global)
      (_hidx : FuncIdxRespectsConcretize mono funcIdx),
      match Source.Eval.runFunction decls name args io₀ fuel,
            Concrete.Eval.runFunction concDecls name args io₀ fuel with
      | .ok (v₁, io₁), .ok (v₂, io₂) =>
          flattenValue decls funcIdx v₁ = Concrete.flattenValue concDecls funcIdx v₂
            ∧ IOBuffer.equiv io₁ io₂
      | .error _, .error _ => True
      | _, _ => False := by
  intro name hnameSrc hnameConc args io₀ fuel funcIdx mono hidx
  exact concretize_preserves_runFunction hmono hdecls hts hconc hcompat name hnameSrc hnameConc
          args io₀ fuel funcIdx mono hidx

-- `MvarFreeDecls` + `AllConcretizeReady` DELETED (orphan, only consumed by
-- the deleted `concretize_ok_of_invariants`).

-- `concretize_ok_of_invariants` DELETED: orphan speculative infra. Only used
-- by the equally-orphan `Typed.Decls.concretize_progress` wrapper below
-- (also deleted). Top-level `Toplevel.compile_progress` gets
-- `∃ concDecls, typedDecls.concretize = .ok concDecls` directly from
-- `WellFormed.monoTerminates` — no need for an intermediate wrapper.
-- Reintroduce if a proof for `Typed.Decls.concretize`'s internal invariants
-- is needed (4-phase decomposition: seed / drain / rewrite / lower).

/-! ## Decomposition of `concretize_layoutMap_progress`

The theorem `∃ lm, cd.layoutMap = .ok lm` follows from two structural
invariants of any `concretize` output `cd`:
1. **RefClosed**: every `.ref g` in `cd`'s types resolves to `.dataType g` in `cd`.
2. **SizeBoundOk**: `DataType.sizeBound` succeeds at every bound/visited combo
   (i.e., the datatype reference graph has no cycles).

These invariants imply `layoutMap` succeeds because `DataType.sizeBound` only
throws on missing refs or cycles, and all size computations in `layoutMap`'s
fold succeed. -/

-- `Concrete.Typ.RefClosed` / `Concrete.Declaration.RefClosed` /
-- `Concrete.Decls.RefClosed` moved up to near `runFunction_preserves_FnFree`.

/-- Acyclicity: `DataType.sizeBound` succeeds at every bound/visited combo
for datatypes registered in `cd` when `visited` is disjoint from all cd
dataType names. This is the tight form: `Typ.sizeBound`'s `.ref` arm enters
with `visited` that never contains cd-dt names (all previous `.ref` traversals
strictly decrease the bound and re-enter `DataType.sizeBound`, which owns
`visited` growth). The `sizeBound_ok_of_rank` proof threads a rank-based
invariant inside the recursion; see `sizeBound_ok_strong`. -/
@[expose] def Concrete.Decls.SizeBoundOk (cd : Concrete.Decls) : Prop :=
  ∀ (bound : Nat) (vis : Std.HashSet Global) (dt : Concrete.DataType),
    (∃ g, cd.getByKey g = some (.dataType dt)) →
    (∀ (g' : Global) (dt' : Concrete.DataType),
        cd.getByKey g' = some (.dataType dt') → ¬ vis.contains dt'.name = true) →
    ∃ n, Concrete.DataType.sizeBound cd bound vis dt = .ok n

/-- `Concrete.Typ.sizeBound` succeeds at any bound/visited combo for a
ref-closed type, given `SizeBoundOk` plus a `visitedDisjoint` side-condition
ruling out revisiting datatypes already in `visited`. -/
private theorem typSizeBound_ok_of_refClosed
    (cd : Concrete.Decls)
    (hac : Concrete.Decls.SizeBoundOk cd) :
    ∀ (bound : Nat) (visited : Std.HashSet Global) (t : Concrete.Typ),
      Concrete.Typ.RefClosed cd t →
      (∀ (g : Global) (dt : Concrete.DataType),
          cd.getByKey g = some (.dataType dt) → ¬ visited.contains dt.name) →
      ∃ n, Concrete.Typ.sizeBound cd bound visited t = .ok n := by
  intro bound
  induction bound with
  | zero =>
    intro visited t _hrc _hv
    refine ⟨0, ?_⟩; unfold Concrete.Typ.sizeBound; rfl
  | succ bound ih =>
    intro visited t hrc hv
    cases t with
    | unit =>
      refine ⟨0, ?_⟩; unfold Concrete.Typ.sizeBound; rfl
    | field =>
      refine ⟨1, ?_⟩; unfold Concrete.Typ.sizeBound; rfl
    | pointer _ =>
      refine ⟨1, ?_⟩; unfold Concrete.Typ.sizeBound; rfl
    | function _ _ =>
      refine ⟨1, ?_⟩; unfold Concrete.Typ.sizeBound; rfl
    | tuple ts =>
      cases hrc
      rename_i hts
      unfold Concrete.Typ.sizeBound
      conv in Array.foldlM _ _ _ => rw [← Array.foldlM_toList]
      simp only [Array.toList_attach, List.attachWith]
      apply List.foldlM_except_ok'
      intro acc t' ht'
      obtain ⟨t'val, ht'mem, ht'eq⟩ := List.mem_pmap.mp ht'
      subst ht'eq
      obtain ⟨m, hm⟩ := ih visited t'val (hts t'val ht'mem) hv
      exact ⟨acc + m, by simp [hm, bind, Except.bind, pure, Except.pure]⟩
    | array inner n =>
      cases hrc
      rename_i hinner
      obtain ⟨m, hm⟩ := ih visited inner hinner hv
      refine ⟨n * m, ?_⟩
      unfold Concrete.Typ.sizeBound
      simp only [hm, bind, Except.bind, pure, Except.pure]
    | ref g =>
      cases hrc
      rename_i hdt
      obtain ⟨dt, hget⟩ := hdt
      unfold Concrete.Typ.sizeBound
      simp only [hget]
      exact hac bound visited dt ⟨g, hget⟩ hv

/-- `Concrete.Typ.size` succeeds under `RefClosed + SizeBoundOk`. Unfolds
to `Typ.sizeBound cd (cd.size + 1) {} t`. The empty `visited` set trivially
satisfies the disjointness precondition. -/
private theorem typSize_ok_of_refClosed
    (cd : Concrete.Decls)
    (hac : Concrete.Decls.SizeBoundOk cd)
    {t : Concrete.Typ}
    (hrc : Concrete.Typ.RefClosed cd t) :
    ∃ n, t.size cd = .ok n := by
  unfold Concrete.Typ.size
  have hdisjoint : ∀ (g : Global) (dt : Concrete.DataType),
      cd.getByKey g = some (.dataType dt) →
      ¬ (({} : Std.HashSet Global)).contains dt.name := by
    intro g dt _hget
    simp only [Std.HashSet.contains_empty, Bool.false_eq_true, not_false_eq_true]
  exact typSizeBound_ok_of_refClosed cd hac (cd.size + 1) {} t hrc hdisjoint

/-- `Concrete.DataType.size` succeeds when the datatype is registered and its
constructor arg types are ref-closed. Closed via `@[expose]` on the outer
`DataType.size` definition + `SizeBoundOk` hypothesis. -/
private theorem dtSize_ok_of_refClosed
    (cd : Concrete.Decls)
    (hac : Concrete.Decls.SizeBoundOk cd)
    (_hrc : Concrete.Decls.RefClosed cd)
    {dt : Concrete.DataType}
    (hinCd : ∃ g, cd.getByKey g = some (.dataType dt))
    (_hdtRC : ∀ c ∈ dt.constructors, ∀ t ∈ c.argTypes,
        Concrete.Typ.RefClosed cd t) :
    ∃ n, Concrete.DataType.size dt cd = .ok n := by
  have hvis : ∀ (g : Global) (dt' : Concrete.DataType),
      cd.getByKey g = some (.dataType dt') →
      ¬ (({} : Std.HashSet Global)).contains dt'.name = true := by
    intro g dt' _hget
    simp only [Std.HashSet.contains_empty, Bool.false_eq_true, not_false_eq_true]
  have ⟨n, hn⟩ := hac (cd.size + 1) {} dt hinCd hvis
  refine ⟨n, ?_⟩
  unfold Concrete.DataType.size
  exact hn

/-- Named step function for `layoutMap`'s fold. -/
private def layoutMapPass (cd : Concrete.Decls) :
    (LayoutMap × Nat) → Global × Concrete.Declaration →
      Except String (LayoutMap × Nat) :=
  fun (layoutMap, funcIdx) (_, v) => do
    match v with
    | .dataType dataType => do
        let dataTypeSize ← dataType.size cd
        let layoutMap :=
          layoutMap.insert dataType.name (.dataType dataTypeSize)
        let pass := fun (acc, index) (constructor : Concrete.Constructor) => do
          let offsets ← constructor.argTypes.foldlM
              (init := (#[0] : Array Nat))
              (fun (offsets : Array Nat) (typ : Concrete.Typ) => do
                let typSyze ← typ.size cd
                pure $ offsets.push
                  ((offsets[offsets.size - 1]?.getD 0) + typSyze))
          let decl :=
            (.constructor { size := dataTypeSize, offsets, index }
              : Layout)
          let name := dataType.name.pushNamespace constructor.nameHead
          pure (acc.insert name decl, index + 1)
        let (layoutMap, _) ← dataType.constructors.foldlM pass
          (layoutMap, (0 : Nat))
        pure (layoutMap, funcIdx)
    | .function function => do
        let inputSize ← function.inputs.foldlM (init := (0 : Nat))
          (fun (acc : Nat) (x : Local × Concrete.Typ) => do
            let typSize ← x.2.size cd
            pure $ acc + typSize)
        let outputSize ← function.output.size cd
        let offsets ← function.inputs.foldlM
          (init := (#[0] : Array Nat))
          (fun (offsets : Array Nat) (x : Local × Concrete.Typ) => do
            let typSyze ← x.2.size cd
            pure $ offsets.push
              ((offsets[offsets.size - 1]?.getD 0) + typSyze))
        let layoutMap := layoutMap.insert function.name $
          .function { index := funcIdx, inputSize, outputSize, offsets }
        pure (layoutMap, funcIdx + 1)
    | .constructor .. => pure (layoutMap, funcIdx)

/-- Per-step success lemma for the `layoutMap` fold. -/
private theorem layoutMap_step_ok
    (cd : Concrete.Decls)
    (hrc : Concrete.Decls.RefClosed cd)
    (hac : Concrete.Decls.SizeBoundOk cd)
    (acc : LayoutMap × Nat) (p : Global × Concrete.Declaration)
    (hp : p ∈ cd.pairs.toList) :
    ∃ acc', layoutMapPass cd acc p = .ok acc' := by
  obtain ⟨name, decl⟩ := p
  have hget : cd.getByKey name = some decl :=
    IndexMap.getByKey_of_mem_pairs cd name decl hp
  have hrcDecl : Concrete.Declaration.RefClosed cd decl := hrc name decl hget
  unfold layoutMapPass
  cases decl with
  | constructor dt c =>
      simp only
      exact ⟨(acc.1, acc.2), rfl⟩
  | function f =>
      have hrcF : (∀ lt ∈ f.inputs, Concrete.Typ.RefClosed cd lt.snd) ∧
                  Concrete.Typ.RefClosed cd f.output := hrcDecl
      have hInputSize :
          ∃ inputSize, f.inputs.foldlM (init := (0 : Nat))
            (fun (acc : Nat) (x : Local × Concrete.Typ) => do
              let typSize ← x.2.size cd
              pure $ acc + typSize) = .ok inputSize := by
        apply List.foldlM_except_ok'
        intro acc' x hx
        have hrcTyp : Concrete.Typ.RefClosed cd x.2 := hrcF.1 x hx
        obtain ⟨n, hn⟩ := typSize_ok_of_refClosed cd hac hrcTyp
        refine ⟨acc' + n, ?_⟩
        simp [hn, bind, Except.bind, pure, Except.pure]
      obtain ⟨inputSize, hinputSize⟩ := hInputSize
      obtain ⟨outputSize, houtputSize⟩ :=
        typSize_ok_of_refClosed cd hac hrcF.2
      have hOffsets :
          ∃ offsets, f.inputs.foldlM
            (init := (#[0] : Array Nat))
            (fun (offsets : Array Nat) (x : Local × Concrete.Typ) => do
              let typSyze ← x.2.size cd
              pure $ offsets.push
                ((offsets[offsets.size - 1]?.getD 0) + typSyze)) = .ok offsets := by
        apply List.foldlM_except_ok'
        intro acc' x hx
        have hrcTyp : Concrete.Typ.RefClosed cd x.2 := hrcF.1 x hx
        obtain ⟨n, hn⟩ := typSize_ok_of_refClosed cd hac hrcTyp
        refine ⟨acc'.push ((acc'[acc'.size - 1]?.getD 0) + n), ?_⟩
        simp [hn, bind, Except.bind, pure, Except.pure]
      obtain ⟨offsets, hoffsets⟩ := hOffsets
      refine ⟨(acc.1.insert f.name
        (.function { index := acc.2, inputSize, outputSize, offsets }),
        acc.2 + 1), ?_⟩
      simp only [bind, Except.bind, pure, Except.pure] at hinputSize hoffsets
      simp only [hinputSize, houtputSize, hoffsets, bind, Except.bind,
        pure, Except.pure]
  | dataType dt =>
      have hrcDT : ∀ c ∈ dt.constructors, ∀ t ∈ c.argTypes,
          Concrete.Typ.RefClosed cd t := hrcDecl
      obtain ⟨dataTypeSize, hdtSize⟩ :=
        dtSize_ok_of_refClosed cd hac hrc ⟨name, hget⟩ hrcDT
      have hCtorFold :
          ∃ res, dt.constructors.foldlM
            (fun (state : LayoutMap × Nat) (constructor : Concrete.Constructor) => do
              let offsets ← constructor.argTypes.foldlM
                (init := (#[0] : Array Nat))
                (fun (offsets : Array Nat) (typ : Concrete.Typ) => do
                  let typSyze ← typ.size cd
                  pure $ offsets.push
                    ((offsets[offsets.size - 1]?.getD 0) + typSyze))
              let decl :=
                (.constructor { size := dataTypeSize, offsets, index := state.2 }
                  : Layout)
              let name := dt.name.pushNamespace constructor.nameHead
              pure (state.1.insert name decl, state.2 + 1))
            (acc.1.insert dt.name (.dataType dataTypeSize), (0 : Nat))
            = .ok res := by
        apply List.foldlM_except_ok'
        intro state c hc
        have hrcC : ∀ t ∈ c.argTypes, Concrete.Typ.RefClosed cd t :=
          hrcDT c hc
        have hOffs :
            ∃ offs, c.argTypes.foldlM
              (init := (#[0] : Array Nat))
              (fun (offsets : Array Nat) (typ : Concrete.Typ) => do
                let typSyze ← typ.size cd
                pure $ offsets.push
                  ((offsets[offsets.size - 1]?.getD 0) + typSyze)) = .ok offs := by
          apply List.foldlM_except_ok'
          intro acc' t ht
          have hrcT : Concrete.Typ.RefClosed cd t := hrcC t ht
          obtain ⟨n, hn⟩ := typSize_ok_of_refClosed cd hac hrcT
          refine ⟨acc'.push ((acc'[acc'.size - 1]?.getD 0) + n), ?_⟩
          simp [hn, bind, Except.bind, pure, Except.pure]
        obtain ⟨offs, hoffs⟩ := hOffs
        refine ⟨(state.1.insert (dt.name.pushNamespace c.nameHead)
          (.constructor { size := dataTypeSize, offsets := offs, index := state.2 }),
          state.2 + 1), ?_⟩
        simp only [bind, Except.bind, pure, Except.pure] at hoffs
        simp only [hoffs, bind, Except.bind, pure, Except.pure]
      obtain ⟨res, hres⟩ := hCtorFold
      refine ⟨(res.1, acc.2), ?_⟩
      simp only [bind, Except.bind, pure, Except.pure] at hres
      simp only [hdtSize, hres, bind, Except.bind, pure, Except.pure]

/-- `layoutMap` succeeds when `cd` is ref-closed and has acyclic size computation. -/
theorem layoutMap_ok_of_refClosed
    (cd : Concrete.Decls)
    (hrc : Concrete.Decls.RefClosed cd)
    (hac : Concrete.Decls.SizeBoundOk cd) :
    ∃ lm, Concrete.Decls.layoutMap cd = .ok lm := by
  have hrw : Concrete.Decls.layoutMap cd = (do
      let r ← cd.pairs.toList.foldlM (layoutMapPass cd)
        (({}, 0) : LayoutMap × Nat)
      pure r.1) := by
    unfold Concrete.Decls.layoutMap
    simp only [IndexMap.foldlM]
    rw [← Array.foldlM_toList]
    rfl
  rw [hrw]
  have ⟨res, hres⟩ := List.foldlM_except_ok' cd.pairs.toList
    (({}, 0) : LayoutMap × Nat) (layoutMap_step_ok cd hrc hac)
  refine ⟨res.1, ?_⟩
  simp [hres, bind, Except.bind, pure, Except.pure]

/-! ### Helpers shared by `RefClosedBody` and `DirectDagBody`.

These were previously private to `DirectDagBody` (ported from
`MonoDataTypeTraceScratch.lean` on 2026-04-23 and duplicating
`CompilerProgress` content that cannot be imported here due to cycles).
Relocated on 2026-04-23 so `RefClosedBody.L2_*` can use them too. Proof
text is identical to the originals. -/

/-! #### `StrongNewNameShape` preservation through `concretizeDrain`. -/

private theorem concretizeDrainEntry_preserves_StrongNewNameShape
    {decls : Typed.Decls} {state state' : DrainState}
    (hinv : state.StrongNewNameShape decls) (entry : Global × Array Typ)
    (hstep : concretizeDrainEntry decls state entry = .ok state') :
    state'.StrongNewNameShape decls := by
  unfold concretizeDrainEntry at hstep
  simp only [bind, Except.bind, pure, Except.pure] at hstep
  by_cases hseen : state.seen.contains (entry.1, entry.2)
  · simp [hseen] at hstep
    rw [← hstep]; exact hinv
  · simp [hseen] at hstep
    split at hstep
    · rename_i f hf_get
      by_cases hsz : f.params.length = entry.2.size
      · simp [hsz] at hstep
        rw [← hstep]
        refine ⟨?_, ?_⟩
        · intro f' hf'mem
          rcases Array.mem_push.mp hf'mem with hin | heq
          · exact hinv.1 f' hin
          · subst heq
            exact ⟨entry.1, entry.2, f, rfl, hf_get, hsz.symm⟩
        · intro dt hdt
          exact hinv.2 dt hdt
      · simp [hsz] at hstep
    · rename_i dt hdt_get
      by_cases hsz : dt.params.length = entry.2.size
      · simp [hsz] at hstep
        rw [← hstep]
        refine ⟨?_, ?_⟩
        · intro f hf
          exact hinv.1 f hf
        · intro dt' hdt'mem
          rcases Array.mem_push.mp hdt'mem with hin | heq
          · exact hinv.2 dt' hin
          · subst heq
            refine ⟨entry.1, entry.2, dt, rfl, hdt_get, hsz.symm, ?_⟩
            rw [List.map_map]
            apply List.map_congr_left
            intro c _
            rfl
      · simp [hsz] at hstep
    · exact absurd hstep (by intro h; cases h)

private theorem concretizeDrainEntry_list_foldlM_preserves_StrongNewNameShape
    {decls : Typed.Decls}
    (L : List (Global × Array Typ))
    (state0 state' : DrainState)
    (hinv0 : state0.StrongNewNameShape decls)
    (hstep : L.foldlM (concretizeDrainEntry decls) state0 = .ok state') :
    state'.StrongNewNameShape decls := by
  induction L generalizing state0 with
  | nil =>
    simp only [List.foldlM, pure, Except.pure, Except.ok.injEq] at hstep
    rw [← hstep]; exact hinv0
  | cons hd tl ih =>
    simp only [List.foldlM, bind, Except.bind] at hstep
    split at hstep
    · cases hstep
    · rename_i s'' hs''
      have hinv1 : s''.StrongNewNameShape decls :=
        concretizeDrainEntry_preserves_StrongNewNameShape hinv0 hd hs''
      exact ih s'' hinv1 hstep

private theorem concretizeDrainIter_preserves_StrongNewNameShape
    {decls : Typed.Decls} {state state' : DrainState}
    (hinv : state.StrongNewNameShape decls)
    (hstep : concretizeDrainIter decls state = .ok state') :
    state'.StrongNewNameShape decls := by
  unfold concretizeDrainIter at hstep
  rw [← Array.foldlM_toList] at hstep
  let state0 : DrainState := { state with pending := ∅ }
  have hinv0 : state0.StrongNewNameShape decls := hinv
  exact concretizeDrainEntry_list_foldlM_preserves_StrongNewNameShape
    state.pending.toArray.toList state0 state' hinv0 hstep

private theorem concretize_drain_preserves_StrongNewNameShape
    {decls : Typed.Decls} (fuel : Nat) (init : DrainState)
    (hinv : init.StrongNewNameShape decls)
    {drained : DrainState}
    (hdrain : concretizeDrain decls fuel init = .ok drained) :
    drained.StrongNewNameShape decls := by
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
        have hinv' : state'.StrongNewNameShape decls :=
          concretizeDrainIter_preserves_StrongNewNameShape hinv hstate'
        exact ih state' hinv' hdrain

/-! #### `IndexMap` key-uniqueness in pairs. -/

/-- If two pairs in `m.pairs.toList` share a key, they are equal. -/
private theorem indexMap_pairs_key_unique
    {α : Type _} {β : Type _} [BEq α] [Hashable α]
    [EquivBEq α] [LawfulHashable α]
    (m : IndexMap α β) {p₁ p₂ : α × β}
    (h₁ : p₁ ∈ m.pairs.toList) (h₂ : p₂ ∈ m.pairs.toList)
    (hkey : p₁.1 == p₂.1) : p₁ = p₂ := by
  obtain ⟨i, hi, hi_eq⟩ := List.getElem_of_mem h₁
  obtain ⟨j, hj, hj_eq⟩ := List.getElem_of_mem h₂
  rw [Array.length_toList] at hi hj
  have hgi : m.pairs[i]'hi = p₁ := by rw [← hi_eq, Array.getElem_toList]
  have hgj : m.pairs[j]'hj = p₂ := by rw [← hj_eq, Array.getElem_toList]
  have hpii := m.pairsIndexed i hi
  have hpij := m.pairsIndexed j hj
  rw [hgi] at hpii
  rw [hgj] at hpij
  have hcong : m.indices[p₁.1]? = m.indices[p₂.1]? :=
    Std.HashMap.getElem?_congr hkey
  rw [hpii, hpij] at hcong
  simp only [Option.some.injEq] at hcong
  subst hcong
  rw [hgi] at hgj; exact hgj

/-- At most one list index has a given key. -/
private theorem indexMap_pairs_index_unique_of_key
    {α : Type _} {β : Type _} [BEq α] [Hashable α]
    [EquivBEq α] [LawfulHashable α]
    (m : IndexMap α β) {i j : Nat} (hi : i < m.pairs.toList.length)
    (hj : j < m.pairs.toList.length)
    (hkey : ((m.pairs.toList[i]'hi).1 == (m.pairs.toList[j]'hj).1) = true) :
    i = j := by
  rw [Array.length_toList] at hi hj
  rw [Array.getElem_toList, Array.getElem_toList] at hkey
  have hpii := m.pairsIndexed i hi
  have hpij := m.pairsIndexed j hj
  have hcong : m.indices[(m.pairs[i]'hi).1]? = m.indices[(m.pairs[j]'hj).1]? :=
    Std.HashMap.getElem?_congr hkey
  rw [hpii, hpij] at hcong
  exact Option.some.inj hcong

/-- DataType-key bridge for the `step4Lower` fold. Uses
`indexMap_pairs_key_unique` (above) to discharge the post-fold preservation
case where another pair has the same key as the dt-pair: by uniqueness within
`monoDecls.pairs.toList`, that pair must be `(g, .dataType dt)`. -/
private theorem step4Lower_fold_dataType_bridge_inline
    {monoDecls : Typed.Decls} {concDecls : Concrete.Decls}
    {g : Global} {dt : DataType}
    (hmd_get : monoDecls.getByKey g = some (.dataType dt))
    (hfold : monoDecls.foldlM (init := default) step4Lower = .ok concDecls) :
    ∃ cdt, concDecls.getByKey g = some (.dataType cdt) := by
  rw [IndexMap.indexMap_foldlM_eq_list_foldlM] at hfold
  have hmem_ml : (g, Typed.Declaration.dataType dt) ∈ monoDecls.pairs.toList :=
    IndexMap.mem_pairs_of_getByKey _ _ _ hmd_get
  -- Inner induction with strengthened "preserve .dataType-at-g" invariant,
  -- threading membership in `monoDecls.pairs.toList` to invoke
  -- `indexMap_pairs_key_unique` when another pair shares key g.
  have aux : ∀ (xs : List (Global × Typed.Declaration)) (init result : Concrete.Decls)
      (_hsub : ∀ p, p ∈ xs → p ∈ monoDecls.pairs.toList)
      (_hmem : (g, Typed.Declaration.dataType dt) ∈ xs)
      (_hP : init.getByKey g = none ∨ ∃ cdt, init.getByKey g = some (.dataType cdt)),
      xs.foldlM step4Lower init = .ok result →
      ∃ cdt, result.getByKey g = some (.dataType cdt) := by
    intro xs
    induction xs with
    | nil => intro _ _ _ hmem; cases hmem
    | cons hd tl ih =>
      intro init result hsub hmem hP hf
      simp only [List.foldlM_cons, bind, Except.bind] at hf
      cases hstep_h : step4Lower init hd with
      | error _ => rw [hstep_h] at hf; cases hf
      | ok acc' =>
        rw [hstep_h] at hf
        rcases List.mem_cons.mp hmem with hmem_hd | hmem_tl
        · -- hd = (g, .dataType dt). step4Lower inserts .dataType at g.
          subst hmem_hd
          have hP' : ∃ cdt, acc'.getByKey g = some (.dataType cdt) := by
            unfold step4Lower at hstep_h
            simp only [bind, Except.bind, pure, Except.pure] at hstep_h
            split at hstep_h
            · cases hstep_h
            rename_i ctors _hctors
            simp only [Except.ok.injEq] at hstep_h
            subst hstep_h
            exact ⟨_, IndexMap.getByKey_insert_self _ _ _⟩
          have hsub_tl : ∀ p, p ∈ tl → p ∈ monoDecls.pairs.toList :=
            fun p hp => hsub p (List.mem_cons.mpr (Or.inr hp))
          -- Strengthened tail induction: preserve .dataType-at-g.
          have aux2 : ∀ (ys : List (Global × Typed.Declaration)) (s s' : Concrete.Decls)
              (_hsub' : ∀ p, p ∈ ys → p ∈ monoDecls.pairs.toList),
              (∃ cdt, s.getByKey g = some (.dataType cdt)) →
              ys.foldlM step4Lower s = .ok s' →
              ∃ cdt, s'.getByKey g = some (.dataType cdt) := by
            intro ys
            induction ys with
            | nil => intro s s' _ hP hf
                     simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at hf
                     subst hf; exact hP
            | cons hd' tl' ih' =>
              intro s s' hsub' hP hf
              simp only [List.foldlM_cons, bind, Except.bind] at hf
              cases hstep_h' : step4Lower s hd' with
              | error _ => rw [hstep_h'] at hf; cases hf
              | ok s'' =>
                rw [hstep_h'] at hf
                obtain ⟨name', d'⟩ := hd'
                have hsub_tl' : ∀ p, p ∈ tl' → p ∈ monoDecls.pairs.toList :=
                  fun p hp => hsub' p (List.mem_cons.mpr (Or.inr hp))
                by_cases hkn : (name' == g) = true
                · -- By IndexMap key-uniqueness, (name', d') = (g, .dataType dt).
                  have h_hd_in : (name', d') ∈ monoDecls.pairs.toList :=
                    hsub' (name', d') (List.mem_cons.mpr (Or.inl rfl))
                  have h_eq : (name', d') = (g, Typed.Declaration.dataType dt) :=
                    indexMap_pairs_key_unique _ h_hd_in hmem_ml hkn
                  rw [h_eq] at hstep_h'
                  unfold step4Lower at hstep_h'
                  simp only [bind, Except.bind, pure, Except.pure] at hstep_h'
                  split at hstep_h'
                  · cases hstep_h'
                  simp only [Except.ok.injEq] at hstep_h'
                  subst hstep_h'
                  exact ih' _ _ hsub_tl'
                    ⟨_, IndexMap.getByKey_insert_self _ _ _⟩ hf
                · have hne : (name' == g) = false := Bool.not_eq_true _ |>.mp hkn
                  cases d' with
                  | function fn =>
                    unfold step4Lower at hstep_h'
                    simp only [bind, Except.bind, pure, Except.pure] at hstep_h'
                    split at hstep_h'
                    · cases hstep_h'
                    split at hstep_h'
                    · cases hstep_h'
                    split at hstep_h'
                    · cases hstep_h'
                    simp only [Except.ok.injEq] at hstep_h'
                    subst hstep_h'
                    obtain ⟨cdt, hcdt⟩ := hP
                    exact ih' _ _ hsub_tl'
                      ⟨cdt, by rw [IndexMap.getByKey_insert_of_beq_false _ _ hne]; exact hcdt⟩
                      hf
                  | dataType dt' =>
                    unfold step4Lower at hstep_h'
                    simp only [bind, Except.bind, pure, Except.pure] at hstep_h'
                    split at hstep_h'
                    · cases hstep_h'
                    simp only [Except.ok.injEq] at hstep_h'
                    subst hstep_h'
                    obtain ⟨cdt, hcdt⟩ := hP
                    exact ih' _ _ hsub_tl'
                      ⟨cdt, by rw [IndexMap.getByKey_insert_of_beq_false _ _ hne]; exact hcdt⟩
                      hf
                  | constructor dt' c' =>
                    unfold step4Lower at hstep_h'
                    simp only [bind, Except.bind, pure, Except.pure] at hstep_h'
                    split at hstep_h'
                    · cases hstep_h'
                    split at hstep_h'
                    · cases hstep_h'
                    simp only [Except.ok.injEq] at hstep_h'
                    subst hstep_h'
                    obtain ⟨cdt, hcdt⟩ := hP
                    exact ih' _ _ hsub_tl'
                      ⟨cdt, by rw [IndexMap.getByKey_insert_of_beq_false _ _ hne]; exact hcdt⟩
                      hf
          exact aux2 tl acc' result hsub_tl hP' hf
        · -- hd is in tl-context. Either hd has key g (then hd = (g, .dataType dt)
          -- by uniqueness, proceed via dataType insertion) or hd's key ≠ g.
          obtain ⟨name_h, d_h⟩ := hd
          have hsub_tl : ∀ p, p ∈ tl → p ∈ monoDecls.pairs.toList :=
            fun p hp => hsub p (List.mem_cons.mpr (Or.inr hp))
          by_cases hkn : (name_h == g) = true
          · -- By uniqueness, hd = (g, .dataType dt).
            have h_hd_in : (name_h, d_h) ∈ monoDecls.pairs.toList :=
              hsub (name_h, d_h) (List.mem_cons.mpr (Or.inl rfl))
            have h_eq : (name_h, d_h) = (g, Typed.Declaration.dataType dt) :=
              indexMap_pairs_key_unique _ h_hd_in hmem_ml hkn
            rw [h_eq] at hstep_h
            have hP' : ∃ cdt, acc'.getByKey g = some (.dataType cdt) := by
              unfold step4Lower at hstep_h
              simp only [bind, Except.bind, pure, Except.pure] at hstep_h
              split at hstep_h
              · cases hstep_h
              simp only [Except.ok.injEq] at hstep_h
              subst hstep_h
              exact ⟨_, IndexMap.getByKey_insert_self _ _ _⟩
            exact ih acc' result hsub_tl hmem_tl (Or.inr hP') hf
          · have hne : (name_h == g) = false := Bool.not_eq_true _ |>.mp hkn
            have hP' : acc'.getByKey g = none ∨
                ∃ cdt, acc'.getByKey g = some (.dataType cdt) := by
              cases d_h with
              | function fn =>
                unfold step4Lower at hstep_h
                simp only [bind, Except.bind, pure, Except.pure] at hstep_h
                split at hstep_h
                · cases hstep_h
                split at hstep_h
                · cases hstep_h
                split at hstep_h
                · cases hstep_h
                simp only [Except.ok.injEq] at hstep_h
                subst hstep_h
                rcases hP with hp | ⟨cdt, hcdt⟩
                · exact Or.inl (by rw [IndexMap.getByKey_insert_of_beq_false _ _ hne]; exact hp)
                · exact Or.inr ⟨cdt, by rw [IndexMap.getByKey_insert_of_beq_false _ _ hne]; exact hcdt⟩
              | dataType dt_h =>
                unfold step4Lower at hstep_h
                simp only [bind, Except.bind, pure, Except.pure] at hstep_h
                split at hstep_h
                · cases hstep_h
                simp only [Except.ok.injEq] at hstep_h
                subst hstep_h
                rcases hP with hp | ⟨cdt, hcdt⟩
                · exact Or.inl (by rw [IndexMap.getByKey_insert_of_beq_false _ _ hne]; exact hp)
                · exact Or.inr ⟨cdt, by rw [IndexMap.getByKey_insert_of_beq_false _ _ hne]; exact hcdt⟩
              | constructor dt_h c_h =>
                unfold step4Lower at hstep_h
                simp only [bind, Except.bind, pure, Except.pure] at hstep_h
                split at hstep_h
                · cases hstep_h
                split at hstep_h
                · cases hstep_h
                simp only [Except.ok.injEq] at hstep_h
                subst hstep_h
                rcases hP with hp | ⟨cdt, hcdt⟩
                · exact Or.inl (by rw [IndexMap.getByKey_insert_of_beq_false _ _ hne]; exact hp)
                · exact Or.inr ⟨cdt, by rw [IndexMap.getByKey_insert_of_beq_false _ _ hne]; exact hcdt⟩
            exact ih acc' result hsub_tl hmem_tl hP' hf
  apply aux _ _ _ (fun _ hp => hp) hmem_ml _ hfold
  · -- default has none at g
    left
    unfold IndexMap.getByKey
    show ((default : Concrete.Decls).indices[g]?).bind _ = none
    have : (default : Concrete.Decls).indices[g]? = none := by
      show ((default : Std.HashMap Global Nat))[g]? = none
      exact Std.HashMap.getElem?_empty
    rw [this]; rfl

/-- Constructor-key bridge for the `step4Lower` fold. Mirror of
`step4Lower_fold_dataType_bridge_inline` over `.constructor`. -/
private theorem step4Lower_fold_ctor_bridge_inline
    {monoDecls : Typed.Decls} {concDecls : Concrete.Decls}
    {g : Global} {dt : DataType} {c : Constructor}
    (hmd_get : monoDecls.getByKey g = some (.constructor dt c))
    (hfold : monoDecls.foldlM (init := default) step4Lower = .ok concDecls) :
    ∃ cdt cc, concDecls.getByKey g = some (.constructor cdt cc) := by
  rw [IndexMap.indexMap_foldlM_eq_list_foldlM] at hfold
  have hmem_ml : (g, Typed.Declaration.constructor dt c) ∈ monoDecls.pairs.toList :=
    IndexMap.mem_pairs_of_getByKey _ _ _ hmd_get
  have aux : ∀ (xs : List (Global × Typed.Declaration)) (init result : Concrete.Decls)
      (_hsub : ∀ p, p ∈ xs → p ∈ monoDecls.pairs.toList)
      (_hmem : (g, Typed.Declaration.constructor dt c) ∈ xs)
      (_hP : init.getByKey g = none ∨
        ∃ cdt cc, init.getByKey g = some (.constructor cdt cc)),
      xs.foldlM step4Lower init = .ok result →
      ∃ cdt cc, result.getByKey g = some (.constructor cdt cc) := by
    intro xs
    induction xs with
    | nil => intro _ _ _ hmem; cases hmem
    | cons hd tl ih =>
      intro init result hsub hmem hP hf
      simp only [List.foldlM_cons, bind, Except.bind] at hf
      cases hstep_h : step4Lower init hd with
      | error _ => rw [hstep_h] at hf; cases hf
      | ok acc' =>
        rw [hstep_h] at hf
        rcases List.mem_cons.mp hmem with hmem_hd | hmem_tl
        · subst hmem_hd
          have hP' : ∃ cdt cc, acc'.getByKey g = some (.constructor cdt cc) := by
            unfold step4Lower at hstep_h
            simp only [bind, Except.bind, pure, Except.pure] at hstep_h
            split at hstep_h
            · cases hstep_h
            split at hstep_h
            · cases hstep_h
            simp only [Except.ok.injEq] at hstep_h
            subst hstep_h
            exact ⟨_, _, IndexMap.getByKey_insert_self _ _ _⟩
          have hsub_tl : ∀ p, p ∈ tl → p ∈ monoDecls.pairs.toList :=
            fun p hp => hsub p (List.mem_cons.mpr (Or.inr hp))
          have aux2 : ∀ (ys : List (Global × Typed.Declaration)) (s s' : Concrete.Decls)
              (_hsub' : ∀ p, p ∈ ys → p ∈ monoDecls.pairs.toList),
              (∃ cdt cc, s.getByKey g = some (.constructor cdt cc)) →
              ys.foldlM step4Lower s = .ok s' →
              ∃ cdt cc, s'.getByKey g = some (.constructor cdt cc) := by
            intro ys
            induction ys with
            | nil => intro s s' _ hP hf
                     simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at hf
                     subst hf; exact hP
            | cons hd' tl' ih' =>
              intro s s' hsub' hP hf
              simp only [List.foldlM_cons, bind, Except.bind] at hf
              cases hstep_h' : step4Lower s hd' with
              | error _ => rw [hstep_h'] at hf; cases hf
              | ok s'' =>
                rw [hstep_h'] at hf
                obtain ⟨name', d'⟩ := hd'
                have hsub_tl' : ∀ p, p ∈ tl' → p ∈ monoDecls.pairs.toList :=
                  fun p hp => hsub' p (List.mem_cons.mpr (Or.inr hp))
                by_cases hkn : (name' == g) = true
                · have h_hd_in : (name', d') ∈ monoDecls.pairs.toList :=
                    hsub' (name', d') (List.mem_cons.mpr (Or.inl rfl))
                  have h_eq : (name', d') = (g, Typed.Declaration.constructor dt c) :=
                    indexMap_pairs_key_unique _ h_hd_in hmem_ml hkn
                  rw [h_eq] at hstep_h'
                  unfold step4Lower at hstep_h'
                  simp only [bind, Except.bind, pure, Except.pure] at hstep_h'
                  split at hstep_h'
                  · cases hstep_h'
                  split at hstep_h'
                  · cases hstep_h'
                  simp only [Except.ok.injEq] at hstep_h'
                  subst hstep_h'
                  exact ih' _ _ hsub_tl'
                    ⟨_, _, IndexMap.getByKey_insert_self _ _ _⟩ hf
                · have hne : (name' == g) = false := Bool.not_eq_true _ |>.mp hkn
                  cases d' with
                  | function fn =>
                    unfold step4Lower at hstep_h'
                    simp only [bind, Except.bind, pure, Except.pure] at hstep_h'
                    split at hstep_h'
                    · cases hstep_h'
                    split at hstep_h'
                    · cases hstep_h'
                    split at hstep_h'
                    · cases hstep_h'
                    simp only [Except.ok.injEq] at hstep_h'
                    subst hstep_h'
                    obtain ⟨cdt, cc, hcc⟩ := hP
                    exact ih' _ _ hsub_tl' ⟨cdt, cc, by
                      rw [IndexMap.getByKey_insert_of_beq_false _ _ hne]; exact hcc⟩ hf
                  | dataType dt' =>
                    unfold step4Lower at hstep_h'
                    simp only [bind, Except.bind, pure, Except.pure] at hstep_h'
                    split at hstep_h'
                    · cases hstep_h'
                    simp only [Except.ok.injEq] at hstep_h'
                    subst hstep_h'
                    obtain ⟨cdt, cc, hcc⟩ := hP
                    exact ih' _ _ hsub_tl' ⟨cdt, cc, by
                      rw [IndexMap.getByKey_insert_of_beq_false _ _ hne]; exact hcc⟩ hf
                  | constructor dt' c' =>
                    unfold step4Lower at hstep_h'
                    simp only [bind, Except.bind, pure, Except.pure] at hstep_h'
                    split at hstep_h'
                    · cases hstep_h'
                    split at hstep_h'
                    · cases hstep_h'
                    simp only [Except.ok.injEq] at hstep_h'
                    subst hstep_h'
                    obtain ⟨cdt, cc, hcc⟩ := hP
                    exact ih' _ _ hsub_tl' ⟨cdt, cc, by
                      rw [IndexMap.getByKey_insert_of_beq_false _ _ hne]; exact hcc⟩ hf
          exact aux2 tl acc' result hsub_tl hP' hf
        · obtain ⟨name_h, d_h⟩ := hd
          have hsub_tl : ∀ p, p ∈ tl → p ∈ monoDecls.pairs.toList :=
            fun p hp => hsub p (List.mem_cons.mpr (Or.inr hp))
          by_cases hkn : (name_h == g) = true
          · have h_hd_in : (name_h, d_h) ∈ monoDecls.pairs.toList :=
              hsub (name_h, d_h) (List.mem_cons.mpr (Or.inl rfl))
            have h_eq : (name_h, d_h) = (g, Typed.Declaration.constructor dt c) :=
              indexMap_pairs_key_unique _ h_hd_in hmem_ml hkn
            rw [h_eq] at hstep_h
            have hP' : ∃ cdt cc, acc'.getByKey g = some (.constructor cdt cc) := by
              unfold step4Lower at hstep_h
              simp only [bind, Except.bind, pure, Except.pure] at hstep_h
              split at hstep_h
              · cases hstep_h
              split at hstep_h
              · cases hstep_h
              simp only [Except.ok.injEq] at hstep_h
              subst hstep_h
              exact ⟨_, _, IndexMap.getByKey_insert_self _ _ _⟩
            exact ih acc' result hsub_tl hmem_tl (Or.inr hP') hf
          · have hne : (name_h == g) = false := Bool.not_eq_true _ |>.mp hkn
            have hP' : acc'.getByKey g = none ∨
                ∃ cdt cc, acc'.getByKey g = some (.constructor cdt cc) := by
              cases d_h with
              | function fn =>
                unfold step4Lower at hstep_h
                simp only [bind, Except.bind, pure, Except.pure] at hstep_h
                split at hstep_h
                · cases hstep_h
                split at hstep_h
                · cases hstep_h
                split at hstep_h
                · cases hstep_h
                simp only [Except.ok.injEq] at hstep_h
                subst hstep_h
                rcases hP with hp | ⟨cdt, cc, hcc⟩
                · exact Or.inl (by rw [IndexMap.getByKey_insert_of_beq_false _ _ hne]; exact hp)
                · exact Or.inr ⟨cdt, cc, by rw [IndexMap.getByKey_insert_of_beq_false _ _ hne]; exact hcc⟩
              | dataType dt_h =>
                unfold step4Lower at hstep_h
                simp only [bind, Except.bind, pure, Except.pure] at hstep_h
                split at hstep_h
                · cases hstep_h
                simp only [Except.ok.injEq] at hstep_h
                subst hstep_h
                rcases hP with hp | ⟨cdt, cc, hcc⟩
                · exact Or.inl (by rw [IndexMap.getByKey_insert_of_beq_false _ _ hne]; exact hp)
                · exact Or.inr ⟨cdt, cc, by rw [IndexMap.getByKey_insert_of_beq_false _ _ hne]; exact hcc⟩
              | constructor dt_h c_h =>
                unfold step4Lower at hstep_h
                simp only [bind, Except.bind, pure, Except.pure] at hstep_h
                split at hstep_h
                · cases hstep_h
                split at hstep_h
                · cases hstep_h
                simp only [Except.ok.injEq] at hstep_h
                subst hstep_h
                rcases hP with hp | ⟨cdt, cc, hcc⟩
                · exact Or.inl (by rw [IndexMap.getByKey_insert_of_beq_false _ _ hne]; exact hp)
                · exact Or.inr ⟨cdt, cc, by rw [IndexMap.getByKey_insert_of_beq_false _ _ hne]; exact hcc⟩
            exact ih acc' result hsub_tl hmem_tl hP' hf
  apply aux _ _ _ (fun _ hp => hp) hmem_ml _ hfold
  · left
    unfold IndexMap.getByKey
    show ((default : Concrete.Decls).indices[g]?).bind _ = none
    have : (default : Concrete.Decls).indices[g]? = none := by
      show ((default : Std.HashMap Global Nat))[g]? = none
      exact Std.HashMap.getElem?_empty
    rw [this]; rfl

/-- `step4Lower` fold lifts `Typed.Decls.TermRefsDt monoDecls` to
`Concrete.Decls.TermRefsDt cd` — assembled via `step4Lower_fold_function_origin`
(F=0 above), `step4Lower_fold_dataType_bridge_inline` /
`step4Lower_fold_ctor_bridge_inline` (F=0 above) for the dt/ctor bridge, and
`termToConcrete_preserves_RefsDt`. -/
private theorem step4Lower_fold_preserves_TermRefsDt
    {monoDecls : Typed.Decls} {concDecls : Concrete.Decls}
    (hmdRef : Typed.Decls.TermRefsDt monoDecls)
    (hfold : monoDecls.foldlM (init := default) step4Lower = .ok concDecls) :
    Concrete.Decls.TermRefsDt concDecls := by
  intro g cf hcf_get
  -- Step (1): function-origin inversion.
  obtain ⟨f, hmd_get, hbody_eq⟩ :=
    step4Lower_fold_function_origin hcf_get hfold
  -- Step (2): typed-side body has RefsDt monoDecls.
  have hbody_typed : Typed.Term.RefsDt monoDecls f.body := hmdRef g f hmd_get
  -- Step (3): bridge monoDecls dt/ctor keys to concDecls dt/ctor keys.
  have hwit : ∀ g',
      ((∃ dt, monoDecls.getByKey g' = some (.dataType dt)) ∨
       (∃ dt c, monoDecls.getByKey g' = some (.constructor dt c))) →
      ((∃ dt, concDecls.getByKey g' = some (.dataType dt)) ∨
       (∃ dt c, concDecls.getByKey g' = some (.constructor dt c))) := by
    intro g' hmd
    rcases hmd with ⟨dt, hdt⟩ | ⟨dt, c, hctor⟩
    · exact Or.inl (step4Lower_fold_dataType_bridge_inline hdt hfold)
    · exact Or.inr (step4Lower_fold_ctor_bridge_inline hctor hfold)
  -- Step (4): apply termToConcrete_preserves_RefsDt.
  exact termToConcrete_preserves_RefsDt hbody_typed hwit hbody_eq

/-- **Top-level: `concretize` preserves `TermRefsDt` from typed to concrete.**

Under `NoTermRefsToFunctions t` (every `.ref g` subterm in source bodies is
keyed to a dt/ctor in `tds`), the concrete `cd` has the same property:
every concrete function body in `cd` has all `.ref g'` subterms keyed to a
dt/ctor in `cd`.

The proof composes:
1. **Drain invariant** (F=0): `NewFunctionsTermRefsDt` survives the worklist
   drain — closed via `concretize_drain_preserves_NewFunctionsTermRefsDt`
   (mechanical 4-level chain matching `NewFunctionsFO`).
2. **`concretizeBuild` preservation** (F=0 via bridges): typed-side
   `TermRefsDt` survives the 3-fold over `monoDecls`.
3. **`step4Lower` fold preservation** (F=0 via per-arm + bridges):
   `Typed.Decls.TermRefsDt monoDecls → Concrete.Decls.TermRefsDt concDecls`. -/
theorem concretize_preserves_TermRefsDt
    {t : Source.Toplevel} {tds : Typed.Decls} {cd : Concrete.Decls}
    (hsrc : NoTermRefsToFunctions t)
    (hts : t.checkAndSimplify = .ok tds)
    (hparamsEmpty : ∀ g f, tds.getByKey g = some (.function f) → f.params = [])
    (hconc : tds.concretize = .ok cd) :
    Concrete.Decls.TermRefsDt cd := by
  -- Reduce `NoTermRefsToFunctions t` + `hts` to typed-side `TermRefsDt tds`.
  have htdsRef : Typed.Decls.TermRefsDt tds := hsrc tds hts
  -- Unpack `concretize` into its 3 stages.
  unfold Typed.Decls.concretize at hconc
  simp only [bind, Except.bind] at hconc
  split at hconc
  · rename_i err _ ; cases hconc
  rename_i drained hdrain
  -- Stage 2: drain produces newFunctions all of which satisfy `Typed.Term.RefsDt tds`.
  have hinit : DrainState.NewFunctionsTermRefsDt tds
      { pending := concretizeSeed tds, seen := {}, mono := {},
        newFunctions := #[], newDataTypes := #[] } :=
    DrainState.NewFunctionsTermRefsDt.init _
  have hnfRef : ∀ f ∈ drained.newFunctions, Typed.Term.RefsDt tds f.body :=
    concretize_drain_preserves_NewFunctionsTermRefsDt htdsRef hparamsEmpty
      _ _ hinit hdrain
  -- Stage 3 (concretizeBuild): typed-side TermRefsDt on the resulting monoDecls.
  have hmdRef : Typed.Decls.TermRefsDt
      (concretizeBuild tds drained.mono drained.newFunctions drained.newDataTypes) :=
    concretizeBuild_preserves_TermRefsDt htdsRef hnfRef
  -- Stage 4 (step4Lower fold): concrete-side TermRefsDt.
  exact step4Lower_fold_preserves_TermRefsDt hmdRef hconc

/-! #### `step4Lower` key-level helpers. -/

/-- `step4Lower` on a `.dataType` input inserts a `.dataType` at the input key. -/
private theorem step4Lower_dataType_shape
    {acc : Concrete.Decls} {name : Global} {dt : DataType}
    {r : Concrete.Decls}
    (hstep : step4Lower acc (name, .dataType dt) = .ok r) :
    ∃ cdt : Concrete.DataType,
      r.getByKey name = some (.dataType cdt) := by
  unfold step4Lower at hstep
  simp only [bind, Except.bind, pure, Except.pure] at hstep
  split at hstep
  · cases hstep
  rename_i ctors _hctors
  simp only [Except.ok.injEq] at hstep
  subst hstep
  exact ⟨_, IndexMap.getByKey_insert_self _ _ _⟩

/-- `step4Lower` on a `.function` input inserts a `.function` at the input key. -/
private theorem step4Lower_function_shape
    {acc : Concrete.Decls} {name : Global} {f : Typed.Function}
    {r : Concrete.Decls}
    (hstep : step4Lower acc (name, .function f) = .ok r) :
    ∃ cf : Concrete.Function,
      r.getByKey name = some (.function cf) := by
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
  exact ⟨_, IndexMap.getByKey_insert_self _ _ _⟩

/-- `step4Lower` on a `.constructor` input inserts a `.constructor` at the input key. -/
private theorem step4Lower_constructor_shape
    {acc : Concrete.Decls} {name : Global} {dt : DataType} {c : Constructor}
    {r : Concrete.Decls}
    (hstep : step4Lower acc (name, .constructor dt c) = .ok r) :
    ∃ (cdt : Concrete.DataType) (cc : Concrete.Constructor),
      r.getByKey name = some (.constructor cdt cc) := by
  unfold step4Lower at hstep
  simp only [bind, Except.bind, pure, Except.pure] at hstep
  split at hstep
  · cases hstep
  split at hstep
  · cases hstep
  simp only [Except.ok.injEq] at hstep
  subst hstep
  exact ⟨_, _, IndexMap.getByKey_insert_self _ _ _⟩

/-- Length-preservation for `List.mapM` in the `Except` monad. -/
private theorem List.mapM_except_ok_length {α β ε : Type}
    {f : α → Except ε β} : ∀ {l : List α} {ls : List β},
    l.mapM f = .ok ls → ls.length = l.length
  | [], ls, h => by
    simp only [_root_.List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h; rfl
  | x :: xs, ls, h => by
    simp only [_root_.List.mapM_cons, bind, Except.bind] at h
    split at h
    · cases h
    rename_i fx _
    split at h
    · cases h
    rename_i fxs hfxs
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    have ih := List.mapM_except_ok_length (f := f) (l := xs) (ls := fxs) hfxs
    simp [_root_.List.length_cons, ih]

/-- Per-position correspondence for `List.mapM` in the `Except` monad. -/
private theorem List.mapM_except_ok_getElem {α β ε : Type}
    {f : α → Except ε β} : ∀ {l : List α} {ls : List β}
    (h : l.mapM f = .ok ls)
    (i : Nat) (hi : i < l.length),
    f (l[i]'hi) = .ok (ls[i]'(by
      rw [List.mapM_except_ok_length h]; exact hi))
  | [], _, _, _, hi => by cases hi
  | x :: xs, ls, h, i, hi => by
    simp only [_root_.List.mapM_cons, bind, Except.bind] at h
    split at h
    · cases h
    rename_i fx hfx
    split at h
    · cases h
    rename_i fxs hfxs
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    cases i with
    | zero => simpa using hfx
    | succ j =>
      have hj : j < xs.length := by
        simp only [_root_.List.length_cons] at hi; omega
      have ih := List.mapM_except_ok_getElem (f := f) hfxs j hj
      simpa using ih

/-- Explicit-structure version of `step4Lower_constructor_shape`: when
`step4Lower` processes `(name, .constructor dt c)`, the resulting decls at
`name` is `.constructor cdt cc` where `cdt.constructors.length =
dt.constructors.length`, `cc.nameHead = c.nameHead`, and the inner
constructor `nameHead`s correspond positionally. -/
private theorem step4Lower_constructor_step_explicit
    {acc : Concrete.Decls} {name : Global} {dt : DataType} {c : Constructor}
    {r : Concrete.Decls}
    (hstep : step4Lower acc (name, .constructor dt c) = .ok r) :
    ∃ cdt cc,
      r.getByKey name = some (.constructor cdt cc) ∧
      cdt.constructors.length = dt.constructors.length ∧
      cc.nameHead = c.nameHead ∧
      (∀ i (hi : i < dt.constructors.length) (hi' : i < cdt.constructors.length),
        (cdt.constructors[i]'hi').nameHead = (dt.constructors[i]'hi).nameHead) ∧
      -- New conjunct: at any position i where dt.constructors[i] = c,
      -- the i-th cdt constructor equals cc.
      (∀ i (hi : i < dt.constructors.length) (hi' : i < cdt.constructors.length),
        (dt.constructors[i]'hi) = c → (cdt.constructors[i]'hi') = cc) := by
  unfold step4Lower at hstep
  simp only [bind, Except.bind, pure, Except.pure] at hstep
  split at hstep
  · cases hstep
  rename_i ctors hctors
  split at hstep
  · cases hstep
  rename_i argTypes hargTypes
  simp only [Except.ok.injEq] at hstep
  subst hstep
  -- Now ctors = dt.constructors.mapM (...), and the result is
  -- acc.insert name (.constructor { name := dt.name, constructors := ctors }
  --                              { nameHead := c.nameHead, argTypes }).
  refine ⟨{ name := dt.name, constructors := ctors },
          { nameHead := c.nameHead, argTypes },
          IndexMap.getByKey_insert_self _ _ _,
          ?_, rfl, ?_, ?_⟩
  · exact List.mapM_except_ok_length hctors
  · intro i hi _hi'
    -- For each i, the i-th element of ctors is built from dt.constructors[i].
    have hget := List.mapM_except_ok_getElem hctors i hi
    -- hget : (do let argTypes ← (dt.constructors[i]).argTypes.mapM ...; pure ...) = .ok ctors[i]
    simp only [bind, Except.bind, pure, Except.pure] at hget
    split at hget
    · cases hget
    rename_i argTypes_i _
    simp only [Except.ok.injEq] at hget
    -- hget : { nameHead := dt.constructors[i].nameHead, argTypes := argTypes_i } = ctors[i]
    rw [← hget]
  · intro i hi _hi' hci
    -- At position i where dt.constructors[i] = c, ctors[i] = cc.
    have hget := List.mapM_except_ok_getElem hctors i hi
    simp only [bind, Except.bind, pure, Except.pure] at hget
    split at hget
    · cases hget
    rename_i argTypes_i hargTypes_i
    simp only [Except.ok.injEq] at hget
    -- argTypes_i is from dt.constructors[i].argTypes.mapM = c.argTypes.mapM = .ok argTypes.
    rw [hci] at hargTypes_i
    -- Now hargTypes_i : c.argTypes.mapM typToConcrete = .ok argTypes_i.
    -- Combined with hargTypes : c.argTypes.mapM typToConcrete = .ok argTypes
    -- we get argTypes_i = argTypes.
    rw [hargTypes] at hargTypes_i
    cases hargTypes_i
    -- ctors[i] = { nameHead := dt.constructors[i].nameHead, argTypes := argTypes }.
    -- We want: ctors[i] = { nameHead := c.nameHead, argTypes := argTypes }.
    -- Since dt.constructors[i] = c, dt.constructors[i].nameHead = c.nameHead. Done.
    rw [← hget, hci]

/-- `step4Lower` preserves `getByKey g` across an insertion at `name ≠ g`. -/
private theorem step4Lower_preserves_other_key
    {acc : Concrete.Decls} {name : Global} {d : Typed.Declaration}
    {r : Concrete.Decls} {g : Global}
    (hstep : step4Lower acc (name, d) = .ok r) (hne_beq : (name == g) = false) :
    r.getByKey g = acc.getByKey g := by
  unfold step4Lower at hstep
  cases d with
  | function f =>
    simp only [bind, Except.bind, pure, Except.pure] at hstep
    split at hstep
    · cases hstep
    split at hstep
    · cases hstep
    split at hstep
    · cases hstep
    simp only [Except.ok.injEq] at hstep
    subst hstep
    exact IndexMap.getByKey_insert_of_beq_false _ _ hne_beq
  | dataType dt =>
    simp only [bind, Except.bind, pure, Except.pure] at hstep
    split at hstep
    · cases hstep
    simp only [Except.ok.injEq] at hstep
    subst hstep
    exact IndexMap.getByKey_insert_of_beq_false _ _ hne_beq
  | constructor dt c =>
    simp only [bind, Except.bind, pure, Except.pure] at hstep
    split at hstep
    · cases hstep
    split at hstep
    · cases hstep
    simp only [Except.ok.injEq] at hstep
    subst hstep
    exact IndexMap.getByKey_insert_of_beq_false _ _ hne_beq

/-- If no element of `xs` has key `g`, then `foldlM step4Lower` preserves
`getByKey g`. -/
private theorem step4Lower_foldlM_no_key_preserves
    {g : Global} :
    ∀ (xs : List (Global × Typed.Declaration))
      (_hne : ∀ p ∈ xs, (p.1 == g) = false)
      (init : Concrete.Decls) (result : Concrete.Decls),
      _root_.List.foldlM step4Lower init xs = .ok result →
      result.getByKey g = init.getByKey g
  | [], _, _, _, hfold => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at hfold
    subst hfold; rfl
  | hd :: tl, hne, init, result, hfold => by
    simp only [List.foldlM_cons, bind, Except.bind] at hfold
    cases hstep : step4Lower init hd with
    | error e => rw [hstep] at hfold; cases hfold
    | ok acc' =>
      rw [hstep] at hfold
      have hhd_ne : (hd.1 == g) = false := hne hd List.mem_cons_self
      have hacc' : acc'.getByKey g = init.getByKey g := by
        obtain ⟨name, d⟩ := hd
        exact step4Lower_preserves_other_key hstep hhd_ne
      have ih := step4Lower_foldlM_no_key_preserves tl
        (fun p hp => hne p (List.mem_cons_of_mem _ hp)) acc' result hfold
      rw [ih, hacc']

/-- Shape trace: if `monoDecls.getByKey g = some d_mono`, then `cd.getByKey g`
matches the kind of `d_mono`. -/
private theorem step4Lower_fold_kind_at_key
    {monoDecls : Typed.Decls} {concDecls : Concrete.Decls}
    {g : Global} {d_mono : Typed.Declaration}
    (hget_mono : monoDecls.getByKey g = some d_mono)
    (hfold : monoDecls.foldlM (init := default) step4Lower = .ok concDecls) :
    (match d_mono with
     | .function _ => ∃ cf, concDecls.getByKey g = some (.function cf)
     | .dataType _ => ∃ cdt, concDecls.getByKey g = some (.dataType cdt)
     | .constructor _ _ => ∃ cdt c, concDecls.getByKey g = some (.constructor cdt c)) := by
  rw [IndexMap.indexMap_foldlM_eq_list_foldlM] at hfold
  have hmem : (g, d_mono) ∈ monoDecls.pairs.toList :=
    IndexMap.mem_pairs_of_getByKey _ _ _ hget_mono
  -- Key uniqueness: every pair with key g equals (g, d_mono).
  have hunique : ∀ p ∈ monoDecls.pairs.toList,
      (p.1 == g) = true → p = (g, d_mono) := by
    intro p hp hpkey
    exact indexMap_pairs_key_unique _ hp hmem hpkey
  -- Split list at the first occurrence of (g, d_mono).
  obtain ⟨pre, post, hsplit⟩ := List.append_of_mem hmem
  have huni' : ∀ p ∈ pre ++ (g, d_mono) :: post,
      (p.1 == g) = true → p = (g, d_mono) := by
    rw [← hsplit]; exact hunique
  have hpre_no_g : ∀ p ∈ pre, (p.1 == g) = false := by
    intro p hp
    rcases hpkey : (p.1 == g) with _ | _
    · rfl
    exfalso
    have hpkey_eq : (p.1 == g) = true := hpkey
    have hp_in_full : p ∈ pre ++ (g, d_mono) :: post := by
      rw [List.mem_append]; exact Or.inl hp
    have hp_eq_gdmono : p = (g, d_mono) := huni' p hp_in_full hpkey_eq
    have hgdm_in_pre : (g, d_mono) ∈ pre := hp_eq_gdmono ▸ hp
    obtain ⟨i, hi_lt, hi_eq⟩ := List.getElem_of_mem hgdm_in_pre
    have hi_lt_full : i < monoDecls.pairs.toList.length := by
      rw [hsplit, List.length_append]
      exact Nat.lt_add_right _ hi_lt
    have hmid_lt_full : pre.length < monoDecls.pairs.toList.length := by
      rw [hsplit, List.length_append]
      exact Nat.lt_add_of_pos_right (Nat.zero_lt_succ _)
    have hlist_i_eq : monoDecls.pairs.toList[i]'hi_lt_full = (g, d_mono) := by
      rw [show monoDecls.pairs.toList[i]'hi_lt_full = (pre ++ (g, d_mono) :: post)[i]'(by
          rw [List.length_append]; exact Nat.lt_add_right _ hi_lt) from by
        congr 1 <;> exact hsplit]
      rw [List.getElem_append_left hi_lt]; exact hi_eq
    have hlist_mid_eq :
        monoDecls.pairs.toList[pre.length]'hmid_lt_full = (g, d_mono) := by
      rw [show monoDecls.pairs.toList[pre.length]'hmid_lt_full =
          (pre ++ (g, d_mono) :: post)[pre.length]'(by
            rw [List.length_append]
            exact Nat.lt_add_of_pos_right (Nat.zero_lt_succ _)) from by
        congr 1 <;> exact hsplit]
      rw [List.getElem_append_right (Nat.le_refl _)]
      simp
    have hkey_eq : ((monoDecls.pairs.toList[i]'hi_lt_full).1 ==
        (monoDecls.pairs.toList[pre.length]'hmid_lt_full).1) = true := by
      rw [hlist_i_eq, hlist_mid_eq]; simp
    have hij := indexMap_pairs_index_unique_of_key monoDecls hi_lt_full hmid_lt_full hkey_eq
    omega
  have hpost_no_g : ∀ p ∈ post, (p.1 == g) = false := by
    intro p hp
    rcases hpkey : (p.1 == g) with _ | _
    · rfl
    exfalso
    have hpkey_eq : (p.1 == g) = true := hpkey
    have hp_in_full : p ∈ pre ++ (g, d_mono) :: post := by
      rw [List.mem_append]
      exact Or.inr (List.mem_cons_of_mem _ hp)
    have hp_eq_gdmono : p = (g, d_mono) := huni' p hp_in_full hpkey_eq
    have hgdm_in_post : (g, d_mono) ∈ post := hp_eq_gdmono ▸ hp
    obtain ⟨i, hi_lt, hi_eq⟩ := List.getElem_of_mem hgdm_in_post
    have hipost_lt_full : pre.length + (i + 1) < monoDecls.pairs.toList.length := by
      rw [hsplit, List.length_append]
      simp [List.length_cons]
      omega
    have hmid_lt_full : pre.length < monoDecls.pairs.toList.length := by
      rw [hsplit, List.length_append]
      exact Nat.lt_add_of_pos_right (Nat.zero_lt_succ _)
    have hlist_ipost :
        monoDecls.pairs.toList[pre.length + (i + 1)]'hipost_lt_full = (g, d_mono) := by
      rw [show monoDecls.pairs.toList[pre.length + (i + 1)]'hipost_lt_full =
          (pre ++ (g, d_mono) :: post)[pre.length + (i + 1)]'(by
            rw [List.length_append]; simp [List.length_cons]; omega) from by
        congr 1 <;> exact hsplit]
      rw [List.getElem_append_right (by omega : pre.length ≤ pre.length + (i + 1))]
      simp
      exact hi_eq
    have hlist_mid :
        monoDecls.pairs.toList[pre.length]'hmid_lt_full = (g, d_mono) := by
      rw [show monoDecls.pairs.toList[pre.length]'hmid_lt_full =
          (pre ++ (g, d_mono) :: post)[pre.length]'(by
            rw [List.length_append]
            exact Nat.lt_add_of_pos_right (Nat.zero_lt_succ _)) from by
        congr 1 <;> exact hsplit]
      rw [List.getElem_append_right (Nat.le_refl _)]
      simp
    have hkey_eq : ((monoDecls.pairs.toList[pre.length + (i + 1)]'hipost_lt_full).1 ==
        (monoDecls.pairs.toList[pre.length]'hmid_lt_full).1) = true := by
      rw [hlist_ipost, hlist_mid]; simp
    have hij := indexMap_pairs_index_unique_of_key monoDecls hipost_lt_full hmid_lt_full hkey_eq
    omega
  -- Split the foldlM via hsplit.
  rw [hsplit] at hfold
  rw [List.foldlM_append] at hfold
  simp only [bind, Except.bind] at hfold
  cases hpre_res : _root_.List.foldlM step4Lower (default : Concrete.Decls) pre with
  | error e => rw [hpre_res] at hfold; cases hfold
  | ok acc_pre =>
    rw [hpre_res] at hfold
    simp only [List.foldlM_cons, bind, Except.bind] at hfold
    cases hstep_g : step4Lower acc_pre (g, d_mono) with
    | error e => rw [hstep_g] at hfold; cases hfold
    | ok acc_g =>
      rw [hstep_g] at hfold
      have hpost_preserve :=
        step4Lower_foldlM_no_key_preserves post hpost_no_g acc_g concDecls hfold
      rw [hpost_preserve]
      cases d_mono with
      | function f =>
        obtain ⟨cf, hcf⟩ := step4Lower_function_shape hstep_g
        exact ⟨cf, hcf⟩
      | dataType dt =>
        obtain ⟨cdt, hcdt⟩ := step4Lower_dataType_shape hstep_g
        exact ⟨cdt, hcdt⟩
      | constructor dt c =>
        obtain ⟨cdt, cc, hcc⟩ := step4Lower_constructor_shape hstep_g
        exact ⟨cdt, cc, hcc⟩

/-- Explicit-structure version of `step4Lower_constructor_shape` lifted to the
full `foldlM`: when `monoDecls.getByKey g = some (.constructor md_dt md_c)`
and the fold succeeds, the resulting `concDecls` at `g` is
`.constructor cd_dt cd_c` where `cd_dt.constructors.length =
md_dt.constructors.length`, `cd_c.nameHead = md_c.nameHead`, and inner
constructor `nameHead`s correspond positionally. -/
private theorem step4Lower_constructor_explicit
    {monoDecls : Typed.Decls} {concDecls : Concrete.Decls}
    {g : Global} {md_dt : DataType} {md_c : Constructor}
    (hget : monoDecls.getByKey g = some (.constructor md_dt md_c))
    (hfold : monoDecls.foldlM (init := default) step4Lower = .ok concDecls) :
    ∃ cd_dt cd_c,
      concDecls.getByKey g = some (.constructor cd_dt cd_c) ∧
      cd_dt.constructors.length = md_dt.constructors.length ∧
      cd_c.nameHead = md_c.nameHead ∧
      (∀ i (hi : i < md_dt.constructors.length)
          (hi' : i < cd_dt.constructors.length),
        (cd_dt.constructors[i]'hi').nameHead =
          (md_dt.constructors[i]'hi).nameHead) ∧
      -- At any position i where md_dt.constructors[i] = md_c, cd_dt.constructors[i] = cd_c.
      (∀ i (hi : i < md_dt.constructors.length)
          (hi' : i < cd_dt.constructors.length),
        (md_dt.constructors[i]'hi) = md_c → (cd_dt.constructors[i]'hi') = cd_c) := by
  -- Replay `step4Lower_fold_kind_at_key`'s splitting strategy to find the
  -- intermediate accumulator `acc_g` from which the (g, .constructor md_dt md_c)
  -- step is taken, then apply `step4Lower_constructor_step_explicit`.
  rw [IndexMap.indexMap_foldlM_eq_list_foldlM] at hfold
  have hmem : (g, Typed.Declaration.constructor md_dt md_c) ∈ monoDecls.pairs.toList :=
    IndexMap.mem_pairs_of_getByKey _ _ _ hget
  have hunique : ∀ p ∈ monoDecls.pairs.toList,
      (p.1 == g) = true → p = (g, .constructor md_dt md_c) := by
    intro p hp hpkey
    exact indexMap_pairs_key_unique _ hp hmem hpkey
  obtain ⟨pre, post, hsplit⟩ := List.append_of_mem hmem
  have huni' : ∀ p ∈ pre ++ (g, .constructor md_dt md_c) :: post,
      (p.1 == g) = true → p = (g, .constructor md_dt md_c) := by
    rw [← hsplit]; exact hunique
  have hpost_no_g : ∀ p ∈ post, (p.1 == g) = false := by
    intro p hp
    rcases hpkey : (p.1 == g) with _ | _
    · rfl
    exfalso
    have hpkey_eq : (p.1 == g) = true := hpkey
    have hp_in_full : p ∈ pre ++ (g, .constructor md_dt md_c) :: post := by
      rw [List.mem_append]
      exact Or.inr (List.mem_cons_of_mem _ hp)
    have hp_eq := huni' p hp_in_full hpkey_eq
    have hgdm_in_post : (g, Typed.Declaration.constructor md_dt md_c) ∈ post :=
      hp_eq ▸ hp
    obtain ⟨i, hi_lt, hi_eq⟩ := List.getElem_of_mem hgdm_in_post
    have hipost_lt_full : pre.length + (i + 1) < monoDecls.pairs.toList.length := by
      rw [hsplit, List.length_append]; simp [List.length_cons]; omega
    have hmid_lt_full : pre.length < monoDecls.pairs.toList.length := by
      rw [hsplit, List.length_append]
      exact Nat.lt_add_of_pos_right (Nat.zero_lt_succ _)
    have hlist_ipost :
        monoDecls.pairs.toList[pre.length + (i + 1)]'hipost_lt_full =
          (g, .constructor md_dt md_c) := by
      rw [show monoDecls.pairs.toList[pre.length + (i + 1)]'hipost_lt_full =
          (pre ++ (g, .constructor md_dt md_c) :: post)[pre.length + (i + 1)]'(by
            rw [List.length_append]; simp [List.length_cons]; omega) from by
        congr 1 <;> exact hsplit]
      rw [List.getElem_append_right (by omega : pre.length ≤ pre.length + (i + 1))]
      simp; exact hi_eq
    have hlist_mid :
        monoDecls.pairs.toList[pre.length]'hmid_lt_full =
          (g, .constructor md_dt md_c) := by
      rw [show monoDecls.pairs.toList[pre.length]'hmid_lt_full =
          (pre ++ (g, .constructor md_dt md_c) :: post)[pre.length]'(by
            rw [List.length_append]
            exact Nat.lt_add_of_pos_right (Nat.zero_lt_succ _)) from by
        congr 1 <;> exact hsplit]
      rw [List.getElem_append_right (Nat.le_refl _)]; simp
    have hkey_eq : ((monoDecls.pairs.toList[pre.length + (i + 1)]'hipost_lt_full).1 ==
        (monoDecls.pairs.toList[pre.length]'hmid_lt_full).1) = true := by
      rw [hlist_ipost, hlist_mid]; simp
    have hij := indexMap_pairs_index_unique_of_key monoDecls hipost_lt_full hmid_lt_full hkey_eq
    omega
  rw [hsplit] at hfold
  rw [List.foldlM_append] at hfold
  simp only [bind, Except.bind] at hfold
  cases hpre_res : _root_.List.foldlM step4Lower (default : Concrete.Decls) pre with
  | error _ => rw [hpre_res] at hfold; cases hfold
  | ok acc_pre =>
    rw [hpre_res] at hfold
    simp only [List.foldlM_cons, bind, Except.bind] at hfold
    cases hstep_g : step4Lower acc_pre (g, .constructor md_dt md_c) with
    | error _ => rw [hstep_g] at hfold; cases hfold
    | ok acc_g =>
      rw [hstep_g] at hfold
      have hpost_preserve :=
        step4Lower_foldlM_no_key_preserves post hpost_no_g acc_g concDecls hfold
      obtain ⟨cdt, cc, hg_acc, hlen, hch, hperpos, hpos_eq⟩ :=
        step4Lower_constructor_step_explicit hstep_g
      refine ⟨cdt, cc, ?_, hlen, hch, hperpos, hpos_eq⟩
      rw [hpost_preserve]; exact hg_acc

/-- Explicit-structure version of `step4Lower_dataType_shape`: when
`step4Lower` processes `(name, .dataType dt)`, the resulting decls at `name`
is `.dataType cdt` where `cdt.constructors.length = dt.constructors.length`
and inner constructor `nameHead`s correspond positionally. -/
private theorem step4Lower_dataType_step_explicit
    {acc : Concrete.Decls} {name : Global} {dt : DataType}
    {r : Concrete.Decls}
    (hstep : step4Lower acc (name, .dataType dt) = .ok r) :
    ∃ cdt,
      r.getByKey name = some (.dataType cdt) ∧
      cdt.constructors.length = dt.constructors.length ∧
      (∀ i (hi : i < dt.constructors.length) (hi' : i < cdt.constructors.length),
        (cdt.constructors[i]'hi').nameHead = (dt.constructors[i]'hi).nameHead) := by
  unfold step4Lower at hstep
  simp only [bind, Except.bind, pure, Except.pure] at hstep
  split at hstep
  · cases hstep
  rename_i ctors hctors
  simp only [Except.ok.injEq] at hstep
  subst hstep
  refine ⟨{ name := dt.name, constructors := ctors },
          IndexMap.getByKey_insert_self _ _ _,
          ?_, ?_⟩
  · exact List.mapM_except_ok_length hctors
  · intro i hi _hi'
    have hget := List.mapM_except_ok_getElem hctors i hi
    simp only [bind, Except.bind, pure, Except.pure] at hget
    split at hget
    · cases hget
    rename_i argTypes_i _
    simp only [Except.ok.injEq] at hget
    rw [← hget]

/-- Explicit-structure version of `step4Lower_dataType_shape` lifted to the
full `foldlM`: when `monoDecls.getByKey g = some (.dataType md_dt)` and the
fold succeeds, the resulting `concDecls` at `g` is `.dataType cdt` with
length and per-position nameHead correspondence to `md_dt`. -/
private theorem step4Lower_dataType_explicit
    {monoDecls : Typed.Decls} {concDecls : Concrete.Decls}
    {g : Global} {md_dt : DataType}
    (hget : monoDecls.getByKey g = some (.dataType md_dt))
    (hfold : monoDecls.foldlM (init := default) step4Lower = .ok concDecls) :
    ∃ cdt,
      concDecls.getByKey g = some (.dataType cdt) ∧
      cdt.constructors.length = md_dt.constructors.length ∧
      (∀ i (hi : i < md_dt.constructors.length)
          (hi' : i < cdt.constructors.length),
        (cdt.constructors[i]'hi').nameHead =
          (md_dt.constructors[i]'hi).nameHead) := by
  -- Replay `step4Lower_constructor_explicit`'s splitting strategy to find the
  -- intermediate accumulator `acc_g` from which the (g, .dataType md_dt) step
  -- is taken, then apply `step4Lower_dataType_step_explicit`.
  rw [IndexMap.indexMap_foldlM_eq_list_foldlM] at hfold
  have hmem : (g, Typed.Declaration.dataType md_dt) ∈ monoDecls.pairs.toList :=
    IndexMap.mem_pairs_of_getByKey _ _ _ hget
  have hunique : ∀ p ∈ monoDecls.pairs.toList,
      (p.1 == g) = true → p = (g, .dataType md_dt) := by
    intro p hp hpkey
    exact indexMap_pairs_key_unique _ hp hmem hpkey
  obtain ⟨pre, post, hsplit⟩ := List.append_of_mem hmem
  have huni' : ∀ p ∈ pre ++ (g, .dataType md_dt) :: post,
      (p.1 == g) = true → p = (g, .dataType md_dt) := by
    rw [← hsplit]; exact hunique
  have hpost_no_g : ∀ p ∈ post, (p.1 == g) = false := by
    intro p hp
    rcases hpkey : (p.1 == g) with _ | _
    · rfl
    exfalso
    have hpkey_eq : (p.1 == g) = true := hpkey
    have hp_in_full : p ∈ pre ++ (g, .dataType md_dt) :: post := by
      rw [List.mem_append]
      exact Or.inr (List.mem_cons_of_mem _ hp)
    have hp_eq := huni' p hp_in_full hpkey_eq
    have hgdm_in_post : (g, Typed.Declaration.dataType md_dt) ∈ post :=
      hp_eq ▸ hp
    obtain ⟨i, hi_lt, hi_eq⟩ := List.getElem_of_mem hgdm_in_post
    have hipost_lt_full : pre.length + (i + 1) < monoDecls.pairs.toList.length := by
      rw [hsplit, List.length_append]; simp [List.length_cons]; omega
    have hmid_lt_full : pre.length < monoDecls.pairs.toList.length := by
      rw [hsplit, List.length_append]
      exact Nat.lt_add_of_pos_right (Nat.zero_lt_succ _)
    have hlist_ipost :
        monoDecls.pairs.toList[pre.length + (i + 1)]'hipost_lt_full =
          (g, .dataType md_dt) := by
      rw [show monoDecls.pairs.toList[pre.length + (i + 1)]'hipost_lt_full =
          (pre ++ (g, .dataType md_dt) :: post)[pre.length + (i + 1)]'(by
            rw [List.length_append]; simp [List.length_cons]; omega) from by
        congr 1 <;> exact hsplit]
      rw [List.getElem_append_right (by omega : pre.length ≤ pre.length + (i + 1))]
      simp; exact hi_eq
    have hlist_mid :
        monoDecls.pairs.toList[pre.length]'hmid_lt_full =
          (g, .dataType md_dt) := by
      rw [show monoDecls.pairs.toList[pre.length]'hmid_lt_full =
          (pre ++ (g, .dataType md_dt) :: post)[pre.length]'(by
            rw [List.length_append]
            exact Nat.lt_add_of_pos_right (Nat.zero_lt_succ _)) from by
        congr 1 <;> exact hsplit]
      rw [List.getElem_append_right (Nat.le_refl _)]; simp
    have hkey_eq : ((monoDecls.pairs.toList[pre.length + (i + 1)]'hipost_lt_full).1 ==
        (monoDecls.pairs.toList[pre.length]'hmid_lt_full).1) = true := by
      rw [hlist_ipost, hlist_mid]; simp
    have hij := indexMap_pairs_index_unique_of_key monoDecls hipost_lt_full hmid_lt_full hkey_eq
    omega
  rw [hsplit] at hfold
  rw [List.foldlM_append] at hfold
  simp only [bind, Except.bind] at hfold
  cases hpre_res : _root_.List.foldlM step4Lower (default : Concrete.Decls) pre with
  | error _ => rw [hpre_res] at hfold; cases hfold
  | ok acc_pre =>
    rw [hpre_res] at hfold
    simp only [List.foldlM_cons, bind, Except.bind] at hfold
    cases hstep_g : step4Lower acc_pre (g, .dataType md_dt) with
    | error _ => rw [hstep_g] at hfold; cases hfold
    | ok acc_g =>
      rw [hstep_g] at hfold
      have hpost_preserve :=
        step4Lower_foldlM_no_key_preserves post hpost_no_g acc_g concDecls hfold
      obtain ⟨cdt, hg_acc, hlen, hperpos⟩ :=
        step4Lower_dataType_step_explicit hstep_g
      refine ⟨cdt, ?_, hlen, hperpos⟩
      rw [hpost_preserve]; exact hg_acc

/-! ### PLAN_3B Phase A.3 — monoDecls↔concDecls ctor kind correspondence (forward).

Trivial specialization of `step4Lower_fold_kind_at_key` to the constructor case. -/
private theorem step4Lower_preserves_ctor_kind_fwd
    {monoDecls : Typed.Decls} {concDecls : Concrete.Decls}
    {g : Global} {dt : DataType} {c : Constructor}
    (hget_mono : monoDecls.getByKey g = some (.constructor dt c))
    (hfold : monoDecls.foldlM (init := default) step4Lower = .ok concDecls) :
    ∃ cdt cd_c, concDecls.getByKey g = some (.constructor cdt cd_c) := by
  have h := step4Lower_fold_kind_at_key hget_mono hfold
  simp only at h
  exact h

/-- Phase A.3 dataType analog: trivial specialization of
`step4Lower_fold_kind_at_key` to the dataType case. -/
private theorem step4Lower_preserves_dataType_kind_fwd
    {monoDecls : Typed.Decls} {concDecls : Concrete.Decls}
    {g : Global} {dt : DataType}
    (hget_mono : monoDecls.getByKey g = some (.dataType dt))
    (hfold : monoDecls.foldlM (init := default) step4Lower = .ok concDecls) :
    ∃ cdt, concDecls.getByKey g = some (.dataType cdt) := by
  have h := step4Lower_fold_kind_at_key hget_mono hfold
  simp only at h
  exact h

/-- Phase A.3 function analog: trivial specialization of
`step4Lower_fold_kind_at_key` to the function case. -/
private theorem step4Lower_preserves_function_kind_fwd
    {monoDecls : Typed.Decls} {concDecls : Concrete.Decls}
    {g : Global} {f : Typed.Function}
    (hget_mono : monoDecls.getByKey g = some (.function f))
    (hfold : monoDecls.foldlM (init := default) step4Lower = .ok concDecls) :
    ∃ cf, concDecls.getByKey g = some (.function cf) := by
  have h := step4Lower_fold_kind_at_key hget_mono hfold
  simp only at h
  exact h

/-! ### PLAN_3B Phase A.2 — typed↔monoDecls ctor kind correspondence.

Trace through the three folds of `concretizeBuild`:
* `fromSource` fold processes the unique `(g, .ctor td_dt td_c)` pair under
  `td_dt.params = []`, inserting `.constructor` at `g`. Other pairs have
  key ≠ `g` (IndexMap key uniqueness) so their inserts don't touch `g`.
* `withNewDts` fold inserts at `dt.name` (`.dataType`) and at
  `dt.name.pushNamespace c.nameHead` (`.constructor`). Under `hDtNotKey`,
  no `.dataType` insertion at `g`. Possible `.constructor` insertion at
  `cName = g` preserves ctor-kind.
* `newFunctions` fold inserts at `f.name` (`.function`). Under `hFnNotKey`,
  no insertion at `g`.
-/

/-- `Global.pushNamespace` strictly extends: no global equals `g.pushNamespace s`.
Follows from `Lean.Name.mkStr` producing a strictly larger `.str` node. -/
private theorem Global.ne_pushNamespace (g : Global) (s : String) :
    g ≠ g.pushNamespace s := by
  intro heq
  have hname : g.toName = Lean.Name.str g.toName s := by
    have : g.toName = (Global.pushNamespace g s).toName := by rw [← heq]
    exact this
  have hlt : sizeOf g.toName < sizeOf (Lean.Name.str g.toName s) := by
    show sizeOf g.toName < 1 + sizeOf g.toName + sizeOf s
    omega
  rw [← hname] at hlt
  exact Nat.lt_irrefl _ hlt

namespace PhaseA2

/-- Local named copy of the `srcStep` lambda from `concretizeBuild`'s
`fromSource` fold. -/
private def srcStep (decls : Typed.Decls) (mono : MonoMap) :
    Typed.Decls → Global × Typed.Declaration → Typed.Decls :=
  fun acc p =>
    let emptySubst : Global → Option Typ := fun _ => none
    let (key, d) := p
    match d with
    | .function f =>
      if f.params.isEmpty then
        acc.insert key (.function
          { f with
            inputs := f.inputs.map fun (l, t) => (l, rewriteTyp emptySubst mono t),
            output := rewriteTyp emptySubst mono f.output,
            body := rewriteTypedTerm decls emptySubst mono f.body })
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
      else acc

/-- Local named copy of the `dtStep` lambda from `concretizeBuild`'s
`withNewDts` fold. -/
private def dtStep (mono : MonoMap) :
    Typed.Decls → DataType → Typed.Decls :=
  fun acc dt =>
    let emptySubst : Global → Option Typ := fun _ => none
    let rewrittenCtors := dt.constructors.map fun c =>
      { c with argTypes := c.argTypes.map (rewriteTyp emptySubst mono) }
    let newDt : DataType := { dt with constructors := rewrittenCtors }
    let acc' := acc.insert dt.name (.dataType newDt)
    rewrittenCtors.foldl
      (fun acc'' c =>
        let cName := dt.name.pushNamespace c.nameHead
        acc''.insert cName (.constructor newDt c))
      acc'

/-- Local named copy of the `fnStep` lambda from `concretizeBuild`'s outer fold. -/
private def fnStep (decls : Typed.Decls) (mono : MonoMap) :
    Typed.Decls → Typed.Function → Typed.Decls :=
  fun acc f =>
    let emptySubst : Global → Option Typ := fun _ => none
    acc.insert f.name (.function
      { f with
        inputs := f.inputs.map fun (l, t) => (l, rewriteTyp emptySubst mono t),
        output := rewriteTyp emptySubst mono f.output,
        body := rewriteTypedTerm decls emptySubst mono f.body })

/-- `concretizeBuild` re-expressed via the named step functions. -/
private theorem concretizeBuild_eq
    (decls : Typed.Decls) (mono : MonoMap)
    (newFunctions : Array Typed.Function) (newDataTypes : Array DataType) :
    concretizeBuild decls mono newFunctions newDataTypes =
      newFunctions.foldl (fnStep decls mono)
        (newDataTypes.foldl (dtStep mono)
          (decls.pairs.foldl (srcStep decls mono) default)) := by
  rfl

/-- A single step of `srcStep` on a pair with key `≠ g` preserves `getByKey g`. -/
private theorem srcStep_preserves_other_key
    (decls : Typed.Decls) (mono : MonoMap)
    {g : Global} (acc : Typed.Decls) (p : Global × Typed.Declaration)
    (hne : (p.1 == g) = false) :
    (srcStep decls mono acc p).getByKey g = acc.getByKey g := by
  unfold srcStep
  obtain ⟨k, d⟩ := p
  cases d with
  | function f =>
    by_cases hp : f.params.isEmpty
    · simp [hp]; rw [IndexMap.getByKey_insert_of_beq_false _ _ hne]
    · simp [hp]
  | dataType dt =>
    by_cases hp : dt.params.isEmpty
    · simp [hp]; rw [IndexMap.getByKey_insert_of_beq_false _ _ hne]
    · simp [hp]
  | constructor dt c =>
    by_cases hp : dt.params.isEmpty
    · simp [hp]; rw [IndexMap.getByKey_insert_of_beq_false _ _ hne]
    · simp [hp]

/-- A `srcStep` foldl over a list with no pair having key `g` preserves `getByKey g`. -/
private theorem srcStep_foldl_no_g_preserves
    (decls : Typed.Decls) (mono : MonoMap) {g : Global} :
    ∀ (xs : List (Global × Typed.Declaration)) (init : Typed.Decls),
      (∀ p ∈ xs, (p.1 == g) = false) →
      (xs.foldl (srcStep decls mono) init).getByKey g = init.getByKey g
  | [], init, _ => rfl
  | p :: rest, init, hne => by
    simp only [List.foldl_cons]
    have h1 : (srcStep decls mono init p).getByKey g = init.getByKey g :=
      srcStep_preserves_other_key decls mono init p (hne p List.mem_cons_self)
    have ih := srcStep_foldl_no_g_preserves decls mono rest (srcStep decls mono init p)
      (fun p' hp' => hne p' (List.mem_cons_of_mem _ hp'))
    rw [ih, h1]

/-- A single step of `srcStep` on the target `(g, .ctor td_dt td_c)` pair under
`td_dt.params = []` produces a `.constructor` entry at `g`. -/
private theorem srcStep_at_g_inserts_ctor
    (decls : Typed.Decls) (mono : MonoMap) (acc : Typed.Decls)
    {g : Global} {td_dt : DataType} {td_c : Constructor}
    (hdt_params : td_dt.params = []) :
    ∃ md_dt md_c,
      (srcStep decls mono acc (g, .constructor td_dt td_c)).getByKey g =
        some (.constructor md_dt md_c) := by
  unfold srcStep
  have hp : td_dt.params.isEmpty = true := by rw [hdt_params]; rfl
  let emptySubst : Global → Option Typ := fun _ => none
  let newCtor : Constructor := { td_c with
    argTypes := td_c.argTypes.map (rewriteTyp emptySubst mono) }
  let newDt : DataType := { td_dt with
    constructors := td_dt.constructors.map fun c' =>
      { c' with argTypes := c'.argTypes.map (rewriteTyp emptySubst mono) } }
  simp only [hp, if_true]
  exact ⟨newDt, newCtor, IndexMap.getByKey_insert_self _ _ _⟩

/-- `fromSource` fold inserts `.constructor` at `g` (split-pattern proof). -/
private theorem fromSource_inserts_ctor_at_key
    (decls : Typed.Decls) (mono : MonoMap)
    {g : Global} {td_dt : DataType} {td_c : Constructor}
    (hget : decls.getByKey g = some (.constructor td_dt td_c))
    (hdt_params : td_dt.params = []) :
    ∃ md_dt md_c,
      (decls.pairs.foldl (srcStep decls mono) default).getByKey g =
        some (.constructor md_dt md_c) := by
  rw [← Array.foldl_toList]
  have hmem : (g, Typed.Declaration.constructor td_dt td_c) ∈ decls.pairs.toList :=
    IndexMap.mem_pairs_of_getByKey _ _ _ hget
  -- Key uniqueness via IndexMap.
  have hunique : ∀ p ∈ decls.pairs.toList,
      (p.1 == g) = true → p = (g, Typed.Declaration.constructor td_dt td_c) := by
    intro p hp hpkey
    exact indexMap_pairs_key_unique _ hp hmem hpkey
  -- Split list at the unique occurrence.
  obtain ⟨pre, post, hsplit⟩ := List.append_of_mem hmem
  -- Pre and post lists have no pair with key g.
  have hno_g_pre : ∀ p ∈ pre, (p.1 == g) = false := by
    intro p hp
    rcases hbeq : (p.1 == g) with _ | _
    · rfl
    · exfalso
      have hp_full : p ∈ decls.pairs.toList := by
        rw [hsplit]; exact List.mem_append_left _ hp
      have hp_eq := hunique p hp_full hbeq
      have hp_in_pre : (g, Typed.Declaration.constructor td_dt td_c) ∈ pre := hp_eq ▸ hp
      -- Same pair appears twice in decls.pairs.toList — contradicts IndexMap uniqueness.
      obtain ⟨i, hi_lt, hi_eq⟩ := List.getElem_of_mem hp_in_pre
      have hi_lt_full : i < decls.pairs.toList.length := by
        rw [hsplit, List.length_append]
        exact Nat.lt_add_right _ hi_lt
      have hmid_lt_full : pre.length < decls.pairs.toList.length := by
        rw [hsplit, List.length_append]
        exact Nat.lt_add_of_pos_right (Nat.zero_lt_succ _)
      have hlist_i : decls.pairs.toList[i]'hi_lt_full =
          (g, Typed.Declaration.constructor td_dt td_c) := by
        rw [show decls.pairs.toList[i]'hi_lt_full =
            (pre ++ (g, Typed.Declaration.constructor td_dt td_c) :: post)[i]'(by
              rw [List.length_append]; exact Nat.lt_add_right _ hi_lt) from by
          congr 1 <;> exact hsplit]
        rw [List.getElem_append_left hi_lt]; exact hi_eq
      have hlist_mid : decls.pairs.toList[pre.length]'hmid_lt_full =
          (g, Typed.Declaration.constructor td_dt td_c) := by
        rw [show decls.pairs.toList[pre.length]'hmid_lt_full =
            (pre ++ (g, Typed.Declaration.constructor td_dt td_c) :: post)[pre.length]'(by
              rw [List.length_append]
              exact Nat.lt_add_of_pos_right (Nat.zero_lt_succ _)) from by
          congr 1 <;> exact hsplit]
        rw [List.getElem_append_right (Nat.le_refl _)]
        simp
      have hkey_eq : ((decls.pairs.toList[i]'hi_lt_full).1 ==
          (decls.pairs.toList[pre.length]'hmid_lt_full).1) = true := by
        rw [hlist_i, hlist_mid]; simp
      have hij := indexMap_pairs_index_unique_of_key decls hi_lt_full hmid_lt_full hkey_eq
      omega
  have hno_g_post : ∀ p ∈ post, (p.1 == g) = false := by
    intro p hp
    rcases hbeq : (p.1 == g) with _ | _
    · rfl
    · exfalso
      have hp_full : p ∈ decls.pairs.toList := by
        rw [hsplit]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hp)
      have hp_eq := hunique p hp_full hbeq
      have hp_in_post : (g, Typed.Declaration.constructor td_dt td_c) ∈ post := hp_eq ▸ hp
      obtain ⟨i, hi_lt, hi_eq⟩ := List.getElem_of_mem hp_in_post
      have hipost_lt_full : pre.length + (i + 1) < decls.pairs.toList.length := by
        rw [hsplit, List.length_append]; simp [List.length_cons]; omega
      have hmid_lt_full : pre.length < decls.pairs.toList.length := by
        rw [hsplit, List.length_append]
        exact Nat.lt_add_of_pos_right (Nat.zero_lt_succ _)
      have hlist_ipost : decls.pairs.toList[pre.length + (i + 1)]'hipost_lt_full =
          (g, Typed.Declaration.constructor td_dt td_c) := by
        rw [show decls.pairs.toList[pre.length + (i + 1)]'hipost_lt_full =
            (pre ++ (g, Typed.Declaration.constructor td_dt td_c) :: post)[pre.length + (i + 1)]'(by
              rw [List.length_append]; simp [List.length_cons]; omega) from by
          congr 1 <;> exact hsplit]
        rw [List.getElem_append_right (by omega : pre.length ≤ pre.length + (i + 1))]
        simp
        exact hi_eq
      have hlist_mid : decls.pairs.toList[pre.length]'hmid_lt_full =
          (g, Typed.Declaration.constructor td_dt td_c) := by
        rw [show decls.pairs.toList[pre.length]'hmid_lt_full =
            (pre ++ (g, Typed.Declaration.constructor td_dt td_c) :: post)[pre.length]'(by
              rw [List.length_append]
              exact Nat.lt_add_of_pos_right (Nat.zero_lt_succ _)) from by
          congr 1 <;> exact hsplit]
        rw [List.getElem_append_right (Nat.le_refl _)]
        simp
      have hkey_eq : ((decls.pairs.toList[pre.length + (i + 1)]'hipost_lt_full).1 ==
          (decls.pairs.toList[pre.length]'hmid_lt_full).1) = true := by
        rw [hlist_ipost, hlist_mid]; simp
      have hij := indexMap_pairs_index_unique_of_key decls hipost_lt_full hmid_lt_full hkey_eq
      omega
  -- Compose.
  rw [hsplit]
  rw [List.foldl_append]
  rw [List.foldl_cons]
  have hpre_eq : (List.foldl (srcStep decls mono) default pre).getByKey g = none := by
    have := srcStep_foldl_no_g_preserves decls mono pre default hno_g_pre
    rw [this]
    -- default IndexMap has none at every key.
    unfold IndexMap.getByKey
    show ((default : Typed.Decls).indices[g]?).bind _ = none
    have : (default : Typed.Decls).indices[g]? = none := by
      show ((default : Std.HashMap Global Nat))[g]? = none
      exact Std.HashMap.getElem?_empty
    rw [this]; rfl
  obtain ⟨md_dt, md_c, hstep⟩ := srcStep_at_g_inserts_ctor decls mono
    (List.foldl (srcStep decls mono) default pre) hdt_params (g := g) (td_dt := td_dt) (td_c := td_c)
  rw [srcStep_foldl_no_g_preserves decls mono post _ hno_g_post]
  exact ⟨md_dt, md_c, hstep⟩

/-- Inner ctor-fold preserves ctor-kind at `g` (each step inserts `.constructor`). -/
private theorem dtCtorFold_preserves_ctor_kind
    (mono : MonoMap) (dt : DataType) (newDt : DataType)
    {g : Global}
    (cs : List Constructor) (acc : Typed.Decls)
    (hacc : ∃ md_dt md_c, acc.getByKey g = some (.constructor md_dt md_c)) :
    ∃ md_dt md_c,
      (cs.foldl
        (fun acc'' c =>
          let cName := dt.name.pushNamespace c.nameHead
          acc''.insert cName (.constructor newDt c))
        acc).getByKey g = some (.constructor md_dt md_c) := by
  induction cs generalizing acc with
  | nil => exact hacc
  | cons c rest ih =>
    simp only [List.foldl_cons]
    apply ih
    by_cases hbeq : (dt.name.pushNamespace c.nameHead == g) = true
    · refine ⟨newDt, c, ?_⟩
      have heq : (dt.name.pushNamespace c.nameHead) = g := LawfulBEq.eq_of_beq hbeq
      show ((acc.insert (dt.name.pushNamespace c.nameHead)
        (.constructor newDt c)).getByKey g) = some (.constructor newDt c)
      rw [heq]
      exact IndexMap.getByKey_insert_self _ _ _
    · have hne : (dt.name.pushNamespace c.nameHead == g) = false :=
        Bool.not_eq_true _ |>.mp hbeq
      obtain ⟨md_dt, md_c, hget⟩ := hacc
      refine ⟨md_dt, md_c, ?_⟩
      show ((acc.insert (dt.name.pushNamespace c.nameHead)
        (.constructor newDt c)).getByKey g) = some (.constructor md_dt md_c)
      rw [IndexMap.getByKey_insert_of_beq_false _ _ hne]
      exact hget

/-- A single step of `dtStep` on a `dt` with `dt.name ≠ g` preserves ctor-kind at `g`. -/
private theorem dtStep_preserves_ctor_kind
    (mono : MonoMap) (acc : Typed.Decls) (dt : DataType)
    {g : Global}
    (hdt_ne : dt.name ≠ g)
    (hacc : ∃ md_dt md_c, acc.getByKey g = some (.constructor md_dt md_c)) :
    ∃ md_dt md_c, (dtStep mono acc dt).getByKey g = some (.constructor md_dt md_c) := by
  unfold dtStep
  have hbeq_dt_name : (dt.name == g) = false := by
    rw [beq_eq_false_iff_ne]; exact hdt_ne
  let emptySubst : Global → Option Typ := fun _ => none
  let rewrittenCtors := dt.constructors.map fun c =>
    { c with argTypes := c.argTypes.map (rewriteTyp emptySubst mono) }
  let newDt : DataType := { dt with constructors := rewrittenCtors }
  have hacc_after_dtinsert : ∃ md_dt md_c,
      (acc.insert dt.name (Typed.Declaration.dataType newDt)).getByKey g =
        some (.constructor md_dt md_c) := by
    obtain ⟨md_dt, md_c, hget⟩ := hacc
    refine ⟨md_dt, md_c, ?_⟩
    rw [IndexMap.getByKey_insert_of_beq_false _ _ hbeq_dt_name]
    exact hget
  exact dtCtorFold_preserves_ctor_kind mono dt newDt rewrittenCtors _ hacc_after_dtinsert

/-- `dtStep` Array foldl preserves ctor-kind at `g` under `hDtNotKey`. -/
private theorem dtStep_foldl_preserves_ctor_kind
    (mono : MonoMap) (newDataTypes : Array DataType) (init : Typed.Decls)
    {g : Global}
    (hinit : ∃ md_dt md_c, init.getByKey g = some (.constructor md_dt md_c))
    (hDtNotKey : ∀ dt ∈ newDataTypes, dt.name ≠ g) :
    ∃ md_dt md_c,
      (newDataTypes.foldl (dtStep mono) init).getByKey g =
        some (.constructor md_dt md_c) := by
  apply Array.foldl_induction
    (motive := fun (_ : Nat) (acc : Typed.Decls) =>
      ∃ md_dt md_c, acc.getByKey g = some (.constructor md_dt md_c)) hinit
  intro i acc hinv
  have hdt_ne : (newDataTypes[i.val]'i.isLt).name ≠ g :=
    hDtNotKey _ (Array.getElem_mem _)
  exact dtStep_preserves_ctor_kind mono acc _ hdt_ne hinv

/-- A single step of `fnStep` on `f` with `f.name ≠ g` preserves ctor-kind at `g`. -/
private theorem fnStep_preserves_ctor_kind
    (decls : Typed.Decls) (mono : MonoMap) (acc : Typed.Decls) (f : Typed.Function)
    {g : Global}
    (hfn_ne : f.name ≠ g)
    (hacc : ∃ md_dt md_c, acc.getByKey g = some (.constructor md_dt md_c)) :
    ∃ md_dt md_c, (fnStep decls mono acc f).getByKey g = some (.constructor md_dt md_c) := by
  unfold fnStep
  have hbeq : (f.name == g) = false := by
    rw [beq_eq_false_iff_ne]; exact hfn_ne
  obtain ⟨md_dt, md_c, hget⟩ := hacc
  refine ⟨md_dt, md_c, ?_⟩
  rw [IndexMap.getByKey_insert_of_beq_false _ _ hbeq]
  exact hget

/-- `fnStep` Array foldl preserves ctor-kind at `g` under `hFnNotKey`. -/
private theorem fnStep_foldl_preserves_ctor_kind
    (decls : Typed.Decls) (mono : MonoMap) (newFunctions : Array Typed.Function)
    (init : Typed.Decls) {g : Global}
    (hinit : ∃ md_dt md_c, init.getByKey g = some (.constructor md_dt md_c))
    (hFnNotKey : ∀ f ∈ newFunctions, f.name ≠ g) :
    ∃ md_dt md_c,
      (newFunctions.foldl (fnStep decls mono) init).getByKey g =
        some (.constructor md_dt md_c) := by
  apply Array.foldl_induction
    (motive := fun (_ : Nat) (acc : Typed.Decls) =>
      ∃ md_dt md_c, acc.getByKey g = some (.constructor md_dt md_c)) hinit
  intro i acc hinv
  have hfn_ne : (newFunctions[i.val]'i.isLt).name ≠ g :=
    hFnNotKey _ (Array.getElem_mem _)
  exact fnStep_preserves_ctor_kind decls mono acc _ hfn_ne hinv

/-- Phase A.2 main: `concretizeBuild` preserves ctor-kind from typed→monoDecls. -/
theorem concretizeBuild_preserves_ctor_kind_fwd
    (decls : Typed.Decls) (mono : MonoMap)
    (newFunctions : Array Typed.Function) (newDataTypes : Array DataType)
    {g : Global} {td_dt : DataType} {td_c : Constructor}
    (hget : decls.getByKey g = some (.constructor td_dt td_c))
    (hdt_params : td_dt.params = [])
    (hDtNotKey : ∀ dt ∈ newDataTypes, dt.name ≠ g)
    (hFnNotKey : ∀ f ∈ newFunctions, f.name ≠ g) :
    ∃ md_dt md_c,
      (concretizeBuild decls mono newFunctions newDataTypes).getByKey g =
        some (.constructor md_dt md_c) := by
  rw [concretizeBuild_eq]
  have h1 := fromSource_inserts_ctor_at_key decls mono hget hdt_params
  have h2 := dtStep_foldl_preserves_ctor_kind mono newDataTypes _ h1 hDtNotKey
  exact fnStep_foldl_preserves_ctor_kind decls mono newFunctions _ h2 hFnNotKey

/-! #### Reverse origin-classification helpers for `concretizeBuild`.

Used by `concretize_under_fullymono_preserves_ctor_kind_bwd` to dispatch the
4 sub-cases of `concretize_build_excludes_polymorphic`. -/

/-- `fnStep` foldl preserves ctor-kind at `g` even without `f.name ≠ g`
hypothesis: if every `f.name ≠ g`, value is unchanged; if some `f.name = g`,
last writer overrides to `.function`, contradicting the ctor witness in init. -/
private theorem fnStep_foldl_no_g_preserves
    (decls : Typed.Decls) (mono : MonoMap) {g : Global} :
    ∀ (xs : List Typed.Function) (init : Typed.Decls),
      (∀ f ∈ xs, f.name ≠ g) →
      (xs.foldl (fnStep decls mono) init).getByKey g = init.getByKey g
  | [], _, _ => rfl
  | f :: rest, init, hne => by
    simp only [List.foldl_cons]
    have h1 : (fnStep decls mono init f).getByKey g = init.getByKey g := by
      unfold fnStep
      have hbeq : (f.name == g) = false := by
        rw [beq_eq_false_iff_ne]; exact hne f List.mem_cons_self
      exact IndexMap.getByKey_insert_of_beq_false _ _ hbeq
    have ih := fnStep_foldl_no_g_preserves decls mono rest (fnStep decls mono init f)
      (fun f' hf' => hne f' (List.mem_cons_of_mem _ hf'))
    rw [ih, h1]

/-- Helper: `dtStep` foldl preserves `getByKey g` when no dt and no
ctor-name in `xs` has key `g`. -/
private theorem dtStep_foldl_no_g_preserves
    (mono : MonoMap) {g : Global} :
    ∀ (xs : List DataType) (init : Typed.Decls),
      (∀ dt ∈ xs, dt.name ≠ g) →
      (∀ dt ∈ xs, ∀ c ∈ dt.constructors,
        dt.name.pushNamespace c.nameHead ≠ g) →
      (xs.foldl (dtStep mono) init).getByKey g = init.getByKey g
  | [], _, _, _ => rfl
  | hd :: tl, init, hno_dt, hno_ctor => by
    simp only [List.foldl_cons]
    have hd_name_ne : hd.name ≠ g := hno_dt hd List.mem_cons_self
    have hd_ctor_ne : ∀ c ∈ hd.constructors,
        hd.name.pushNamespace c.nameHead ≠ g :=
      fun c hc => hno_ctor hd List.mem_cons_self c hc
    have ih := dtStep_foldl_no_g_preserves mono tl (dtStep mono init hd)
      (fun dt hdt => hno_dt dt (List.mem_cons_of_mem _ hdt))
      (fun dt hdt c hc => hno_ctor dt (List.mem_cons_of_mem _ hdt) c hc)
    rw [ih]
    -- dtStep mono init hd preserves getByKey g.
    unfold dtStep
    let emptySubst : Global → Option Typ := fun _ => none
    let rewrittenCtors := hd.constructors.map fun c =>
      { c with argTypes := c.argTypes.map (rewriteTyp emptySubst mono) }
    let newDt : DataType := { hd with constructors := rewrittenCtors }
    have hbeq_dt_name : (hd.name == g) = false := by
      rw [beq_eq_false_iff_ne]; exact hd_name_ne
    have hctor_inner : ∀ (cs : List Constructor) (acc' : Typed.Decls),
        (∀ c ∈ cs, hd.name.pushNamespace c.nameHead ≠ g) →
        IndexMap.getByKey (cs.foldl (fun acc'' c =>
          acc''.insert (hd.name.pushNamespace c.nameHead)
            (.constructor newDt c)) acc') g = acc'.getByKey g := by
      intro cs
      induction cs with
      | nil => intros; rfl
      | cons c0 rest ih_cs =>
        intro acc' hne
        simp only [List.foldl_cons]
        have hnc0 : hd.name.pushNamespace c0.nameHead ≠ g :=
          hne c0 List.mem_cons_self
        have hnc0_beq : (hd.name.pushNamespace c0.nameHead == g) = false := by
          rw [beq_eq_false_iff_ne]; exact hnc0
        rw [ih_cs _ (fun c'' hc'' => hne c'' (List.mem_cons_of_mem _ hc''))]
        exact IndexMap.getByKey_insert_of_beq_false _ _ hnc0_beq
    have hd_rw_ctor_ne : ∀ c ∈ rewrittenCtors,
        hd.name.pushNamespace c.nameHead ≠ g := by
      intro c' hc'
      simp only [List.mem_map, rewrittenCtors] at hc'
      obtain ⟨c0, hc0, hc0_eq⟩ := hc'
      rw [← hc0_eq]
      exact hd_ctor_ne c0 hc0
    rw [hctor_inner _ _ hd_rw_ctor_ne]
    exact IndexMap.getByKey_insert_of_beq_false _ _ hbeq_dt_name

/-- Reverse origin: if `concretizeBuild` has `.constructor` at `g`, then either
source has `.constructor` at `g` with monomorphic params, or there is a
`newDataTypes` constructor whose mangled key matches `g` (origin 4). -/
private theorem concretizeBuild_ctor_origin
    (decls : Typed.Decls) (mono : MonoMap)
    (newFunctions : Array Typed.Function) (newDataTypes : Array DataType)
    {g : Global} {cd_dt : DataType} {cd_c : Constructor}
    (hget : (concretizeBuild decls mono newFunctions newDataTypes).getByKey g =
      some (.constructor cd_dt cd_c)) :
    (∃ src_dt src_c, decls.getByKey g = some (.constructor src_dt src_c) ∧
        src_dt.params = []) ∨
    (∃ dt ∈ newDataTypes, ∃ c ∈ dt.constructors,
        dt.name.pushNamespace c.nameHead = g) := by
  rw [concretizeBuild_eq] at hget
  rw [← Array.foldl_toList] at hget
  rw [show (newDataTypes.foldl (dtStep mono) (decls.pairs.foldl (srcStep decls mono) default))
      = (newDataTypes.toList.foldl (dtStep mono) (decls.pairs.toList.foldl (srcStep decls mono) default))
      from by rw [← Array.foldl_toList, ← Array.foldl_toList]] at hget
  -- Outer `fnStep` fold: every `fnStep` insert produces `.function`.
  -- If any f.name = g, the LAST writer in fnStep fold overrides to .function,
  -- contradicting the .ctor witness.
  by_cases hfn_ex : ∃ f ∈ newFunctions.toList, f.name = g
  · exfalso
    obtain ⟨f, hf_mem, hf_name⟩ := hfn_ex
    -- Split list at f, every fnStep insert produces .function at f.name = g.
    obtain ⟨pre, post, hsplit⟩ := List.append_of_mem hf_mem
    have hfold_decompose : (newFunctions.toList.foldl (fnStep decls mono)
        (newDataTypes.toList.foldl (dtStep mono)
          (decls.pairs.toList.foldl (srcStep decls mono) default))).getByKey g
        = ((post.foldl (fnStep decls mono))
            ((fnStep decls mono)
              (pre.foldl (fnStep decls mono)
                (newDataTypes.toList.foldl (dtStep mono)
                  (decls.pairs.toList.foldl (srcStep decls mono) default))) f)).getByKey g := by
      rw [hsplit, List.foldl_append, List.foldl_cons]
    rw [hfold_decompose] at hget
    -- The mid value (after fnStep on f) has .function at g.
    have hmid_fn : ∃ newF, (fnStep decls mono
        (pre.foldl (fnStep decls mono)
          (newDataTypes.toList.foldl (dtStep mono)
            (decls.pairs.toList.foldl (srcStep decls mono) default))) f).getByKey g
        = some (.function newF) := by
      unfold fnStep
      rw [hf_name]
      exact ⟨_, IndexMap.getByKey_insert_self _ _ _⟩
    -- Post fold preserves .function at g (every step is an insert; if f'.name = g
    -- it stays .function, otherwise unchanged).
    have hpost_pres : ∀ (xs : List Typed.Function) (acc : Typed.Decls),
        (∃ newF, acc.getByKey g = some (.function newF)) →
        ∃ newF, (xs.foldl (fnStep decls mono) acc).getByKey g
          = some (.function newF) := by
      intro xs
      induction xs with
      | nil => intro acc h; exact h
      | cons f' rest ih =>
        intro acc h
        simp only [List.foldl_cons]
        apply ih
        by_cases hbeq : (f'.name == g) = true
        · unfold fnStep
          rw [LawfulBEq.eq_of_beq hbeq]
          exact ⟨_, IndexMap.getByKey_insert_self _ _ _⟩
        · have hne : (f'.name == g) = false := Bool.not_eq_true _ |>.mp hbeq
          obtain ⟨newF, hget⟩ := h
          unfold fnStep
          exact ⟨newF, by rw [IndexMap.getByKey_insert_of_beq_false _ _ hne]; exact hget⟩
    obtain ⟨newF, hnewF⟩ := hpost_pres post _ hmid_fn
    rw [hnewF] at hget
    cases hget
  · -- No fnStep wrote at g. Outer fold preserves getByKey g.
    have hfn_pres : (newFunctions.toList.foldl (fnStep decls mono)
        (newDataTypes.toList.foldl (dtStep mono)
          (decls.pairs.toList.foldl (srcStep decls mono) default))).getByKey g
        = (newDataTypes.toList.foldl (dtStep mono)
          (decls.pairs.toList.foldl (srcStep decls mono) default)).getByKey g := by
      apply fnStep_foldl_no_g_preserves
      intro f hf heq
      exact hfn_ex ⟨f, hf, heq⟩
    rw [hfn_pres] at hget
    -- Now examine dtStep fold. Case-split on origin 3/4 vs neither.
    by_cases hctor_ex : ∃ dt ∈ newDataTypes.toList,
        ∃ c ∈ dt.constructors, dt.name.pushNamespace c.nameHead = g
    · obtain ⟨dt, hdt_mem, c, hc_mem, hc_eq⟩ := hctor_ex
      exact Or.inr ⟨dt, Array.mem_toList_iff.mp hdt_mem, c, hc_mem, hc_eq⟩
    · -- No origin 4. Sub-case on origin 3.
      by_cases hdt_ex : ∃ dt ∈ newDataTypes.toList, dt.name = g
      · -- Origin 3 only: the dtStep at dt.name = g overrides to .dataType.
        -- Then subsequent dtStep_foldl preserves up to LAST origin-3-writer.
        -- We need: last writer for dt.name = g produces .dataType, contradicting .ctor.
        exfalso
        -- Find the LAST dt in newDataTypes.toList with dt.name = g.
        have hlast_dt : ∀ (xs : List DataType) (init : Typed.Decls),
            (∀ dt ∈ xs, ∀ c ∈ dt.constructors,
              dt.name.pushNamespace c.nameHead ≠ g) →
            (∃ dt ∈ xs, dt.name = g) →
            ∃ ddt, (xs.foldl (dtStep mono) init).getByKey g = some (.dataType ddt) := by
          intro xs
          induction xs with
          | nil => intro _ _ ⟨_, hm, _⟩; cases hm
          | cons hd tl ih =>
            intro init hno_ctor hex
            simp only [List.foldl_cons]
            by_cases htl_ex : ∃ dt ∈ tl, dt.name = g
            · exact ih _ (fun dt hdt c hc => hno_ctor dt (List.mem_cons_of_mem _ hdt) c hc)
                htl_ex
            · obtain ⟨dt_ex, hdt_ex_mem, hdt_ex_eq⟩ := hex
              have hdt_is_hd : dt_ex = hd := by
                rcases List.mem_cons.mp hdt_ex_mem with rfl | htl_mem
                · rfl
                · exact absurd ⟨dt_ex, htl_mem, hdt_ex_eq⟩ htl_ex
              subst hdt_is_hd
              -- All tl: dt.name ≠ g (so dtStep_foldl_no_g_preserves applies on tl).
              have hno_dt_tl : ∀ dt' ∈ tl, dt'.name ≠ g := by
                intro dt' hdt' heq
                exact htl_ex ⟨dt', hdt', heq⟩
              have hno_ctor_tl : ∀ dt' ∈ tl, ∀ c' ∈ dt'.constructors,
                  dt'.name.pushNamespace c'.nameHead ≠ g :=
                fun dt' hdt' c' hc' =>
                  hno_ctor dt' (List.mem_cons_of_mem _ hdt') c' hc'
              rw [dtStep_foldl_no_g_preserves mono tl _ hno_dt_tl hno_ctor_tl]
              -- dtStep init dt_ex with dt_ex.name = g: outer insert at dt_ex.name = g
              -- produces .dataType, then inner ctor fold inserts at
              -- dt_ex.name.pushNamespace c.nameHead. Since hno_ctor on dt_ex says
              -- those keys ≠ g, the final value at g is .dataType.
              unfold dtStep
              let emptySubst : Global → Option Typ := fun _ => none
              let rewrittenCtors := dt_ex.constructors.map fun c =>
                { c with argTypes := c.argTypes.map (rewriteTyp emptySubst mono) }
              let newDt : DataType := { dt_ex with constructors := rewrittenCtors }
              have hctor_inner : ∀ (cs : List Constructor) (acc' : Typed.Decls),
                  (∀ c ∈ cs, dt_ex.name.pushNamespace c.nameHead ≠ g) →
                  IndexMap.getByKey (cs.foldl (fun acc'' c =>
                    acc''.insert (dt_ex.name.pushNamespace c.nameHead)
                      (.constructor newDt c)) acc') g = acc'.getByKey g := by
                intro cs
                induction cs with
                | nil => intros; rfl
                | cons c0 rest ih_cs =>
                  intro acc' hne
                  simp only [List.foldl_cons]
                  have hnc0 : dt_ex.name.pushNamespace c0.nameHead ≠ g :=
                    hne c0 List.mem_cons_self
                  have hnc0_beq : (dt_ex.name.pushNamespace c0.nameHead == g) = false := by
                    rw [beq_eq_false_iff_ne]; exact hnc0
                  rw [ih_cs _ (fun c'' hc'' => hne c'' (List.mem_cons_of_mem _ hc''))]
                  exact IndexMap.getByKey_insert_of_beq_false _ _ hnc0_beq
              have hctor_ne : ∀ c ∈ rewrittenCtors,
                  dt_ex.name.pushNamespace c.nameHead ≠ g := by
                intro c' hc'
                simp only [List.mem_map, rewrittenCtors] at hc'
                obtain ⟨c0, hc0, hc0_eq⟩ := hc'
                rw [← hc0_eq]
                exact hno_ctor dt_ex List.mem_cons_self c0 hc0
              show ∃ ddt, IndexMap.getByKey (rewrittenCtors.foldl
                  (fun acc'' c =>
                    acc''.insert (dt_ex.name.pushNamespace c.nameHead)
                      (.constructor newDt c))
                  (init.insert dt_ex.name (.dataType newDt))) g
                = some (.dataType ddt)
              rw [hctor_inner _ _ hctor_ne]
              refine ⟨newDt, ?_⟩
              rw [← hdt_ex_eq]
              exact IndexMap.getByKey_insert_self _ _ _
        have hno_ctor_all : ∀ dt ∈ newDataTypes.toList, ∀ c ∈ dt.constructors,
            dt.name.pushNamespace c.nameHead ≠ g := by
          intro dt hdt c hc heq
          exact hctor_ex ⟨dt, hdt, c, hc, heq⟩
        obtain ⟨ddt_v, hfinal⟩ := hlast_dt newDataTypes.toList _ hno_ctor_all hdt_ex
        rw [hfinal] at hget
        cases hget
      · -- Neither origin 3 nor origin 4: dtStep fold preserves getByKey g.
        have hno_dt_name : ∀ dt ∈ newDataTypes.toList, dt.name ≠ g := by
          intro dt hdt heq; exact hdt_ex ⟨dt, hdt, heq⟩
        have hno_ctor : ∀ dt ∈ newDataTypes.toList, ∀ c ∈ dt.constructors,
            dt.name.pushNamespace c.nameHead ≠ g := by
          intro dt hdt c hc heq; exact hctor_ex ⟨dt, hdt, c, hc, heq⟩
        rw [dtStep_foldl_no_g_preserves mono newDataTypes.toList _
          hno_dt_name hno_ctor] at hget
        -- Now hget says fromSource has .ctor at g. Trace back via srcStep fold.
        left
        have hsrc_shape : ∀ (pairs : List (Global × Typed.Declaration))
            (init : Typed.Decls),
            (∀ p ∈ pairs, decls.getByKey p.1 = some p.2) →
            (pairs.foldl (srcStep decls mono) init).getByKey g
              = some (.constructor cd_dt cd_c) →
            (∃ src_dt src_c, decls.getByKey g = some (.constructor src_dt src_c) ∧
              src_dt.params = []) ∨
            init.getByKey g = some (.constructor cd_dt cd_c) := by
          intro pairs
          induction pairs with
          | nil =>
            intro init _ hfold
            right; exact hfold
          | cons hd tl ih =>
            intro init hpairs hfold
            simp only [List.foldl_cons] at hfold
            have hpairs_tl : ∀ p ∈ tl, decls.getByKey p.1 = some p.2 :=
              fun p hp => hpairs p (List.mem_cons_of_mem _ hp)
            have hpairs_hd : decls.getByKey hd.1 = some hd.2 :=
              hpairs hd List.mem_cons_self
            rcases ih (srcStep decls mono init hd) hpairs_tl hfold with hleft | hmid
            · exact Or.inl hleft
            · obtain ⟨k, dd⟩ := hd
              simp only at hmid hpairs_hd
              cases dd with
              | function f =>
                by_cases hp : f.params.isEmpty = true
                · simp only [srcStep, hp, if_true] at hmid
                  by_cases hk : (k == g) = true
                  · have hkeq : k = g := LawfulBEq.eq_of_beq hk
                    rw [hkeq] at hmid
                    rw [IndexMap.getByKey_insert_self] at hmid
                    cases hmid
                  · have hk' : (k == g) = false := Bool.not_eq_true _ |>.mp hk
                    rw [IndexMap.getByKey_insert_of_beq_false _ _ hk'] at hmid
                    exact Or.inr hmid
                · simp only [srcStep, hp, if_false, Bool.false_eq_true] at hmid
                  exact Or.inr hmid
              | dataType dt =>
                by_cases hp : dt.params.isEmpty = true
                · simp only [srcStep, hp, if_true] at hmid
                  by_cases hk : (k == g) = true
                  · have hkeq : k = g := LawfulBEq.eq_of_beq hk
                    rw [hkeq] at hmid
                    rw [IndexMap.getByKey_insert_self] at hmid
                    cases hmid
                  · have hk' : (k == g) = false := Bool.not_eq_true _ |>.mp hk
                    rw [IndexMap.getByKey_insert_of_beq_false _ _ hk'] at hmid
                    exact Or.inr hmid
                · simp only [srcStep, hp, if_false, Bool.false_eq_true] at hmid
                  exact Or.inr hmid
              | constructor dt c =>
                by_cases hp : dt.params.isEmpty = true
                · simp only [srcStep, hp, if_true] at hmid
                  by_cases hk : (k == g) = true
                  · have hkeq : k = g := LawfulBEq.eq_of_beq hk
                    refine Or.inl ⟨dt, c, ?_, ?_⟩
                    · rw [← hkeq]; exact hpairs_hd
                    · cases hdp : dt.params with
                      | nil => rfl
                      | cons _ _ => rw [hdp] at hp; cases hp
                  · have hk' : (k == g) = false := Bool.not_eq_true _ |>.mp hk
                    rw [IndexMap.getByKey_insert_of_beq_false _ _ hk'] at hmid
                    exact Or.inr hmid
                · simp only [srcStep, hp, if_false, Bool.false_eq_true] at hmid
                  exact Or.inr hmid
        have hdefault_none : (default : Typed.Decls).getByKey g = none := by
          unfold IndexMap.getByKey
          show ((default : Typed.Decls).indices[g]?).bind _ = none
          have : (default : Typed.Decls).indices[g]? = none := by
            show ((default : Std.HashMap Global Nat))[g]? = none
            exact Std.HashMap.getElem?_empty
          rw [this]; rfl
        have hpairs_hyp : ∀ p ∈ decls.pairs.toList, decls.getByKey p.1 = some p.2 := by
          intro p hp
          rcases p with ⟨a, b⟩
          exact IndexMap.getByKey_of_mem_pairs _ _ _ hp
        rcases hsrc_shape decls.pairs.toList default hpairs_hyp hget with hleft | hmid
        · exact hleft
        · rw [hdefault_none] at hmid
          cases hmid

/-! #### Explicit-structure variants of Phase A.2 ctor-kind preservation.

The existential `concretizeBuild_preserves_ctor_kind_fwd` is sufficient for the
A.2 main lemma but downstream proofs (e.g. structural matching against the
typed-side datatype/constructor shape) need to know the *specific* monoDt/monoC
produced by the empty-substitution rewrite. Mirrors the existential chain:
`srcStep_at_g_inserts_ctor` → `fromSource_inserts_ctor_at_key` →
`dtStep_foldl_preserves_ctor_kind` → `fnStep_foldl_preserves_ctor_kind` →
`concretizeBuild_preserves_ctor_kind_fwd`. -/

/-- Explicit-structure variant of `srcStep_at_g_inserts_ctor`: returns the
*specific* `(newDt, newCtor)` produced by the empty-substitution rewrite. -/
private theorem srcStep_at_g_inserts_ctor_explicit
    (decls : Typed.Decls) (mono : MonoMap) (acc : Typed.Decls)
    {g : Global} {td_dt : DataType} {td_c : Constructor}
    (hdt_params : td_dt.params = []) :
    let emptySubst : Global → Option Typ := fun _ => none
    let rewrittenCtors := td_dt.constructors.map fun c' =>
      { c' with argTypes := c'.argTypes.map (rewriteTyp emptySubst mono) }
    let newDt : DataType := { td_dt with constructors := rewrittenCtors }
    let newCtor : Constructor :=
      { td_c with argTypes := td_c.argTypes.map (rewriteTyp emptySubst mono) }
    (srcStep decls mono acc (g, .constructor td_dt td_c)).getByKey g =
      some (.constructor newDt newCtor) := by
  unfold srcStep
  have hp : td_dt.params.isEmpty = true := by rw [hdt_params]; rfl
  simp only [hp, if_true]
  exact IndexMap.getByKey_insert_self _ _ _

/-- Explicit-structure variant of `fromSource_inserts_ctor_at_key`: returns the
*specific* `(newDt, newCtor)` produced by the empty-substitution rewrite. The
proof mirrors the split-pattern proof in `fromSource_inserts_ctor_at_key`,
using `srcStep_at_g_inserts_ctor_explicit` at the unique occurrence. -/
private theorem fromSource_inserts_ctor_at_key_explicit
    (decls : Typed.Decls) (mono : MonoMap)
    {g : Global} {td_dt : DataType} {td_c : Constructor}
    (hget : decls.getByKey g = some (.constructor td_dt td_c))
    (hdt_params : td_dt.params = []) :
    let emptySubst : Global → Option Typ := fun _ => none
    let rewrittenCtors := td_dt.constructors.map fun c' =>
      { c' with argTypes := c'.argTypes.map (rewriteTyp emptySubst mono) }
    let newDt : DataType := { td_dt with constructors := rewrittenCtors }
    let newCtor : Constructor :=
      { td_c with argTypes := td_c.argTypes.map (rewriteTyp emptySubst mono) }
    (decls.pairs.foldl (srcStep decls mono) default).getByKey g =
      some (.constructor newDt newCtor) := by
  rw [← Array.foldl_toList]
  have hmem : (g, Typed.Declaration.constructor td_dt td_c) ∈ decls.pairs.toList :=
    IndexMap.mem_pairs_of_getByKey _ _ _ hget
  have hunique : ∀ p ∈ decls.pairs.toList,
      (p.1 == g) = true → p = (g, Typed.Declaration.constructor td_dt td_c) := by
    intro p hp hpkey
    exact indexMap_pairs_key_unique _ hp hmem hpkey
  obtain ⟨pre, post, hsplit⟩ := List.append_of_mem hmem
  have hno_g_pre : ∀ p ∈ pre, (p.1 == g) = false := by
    intro p hp
    rcases hbeq : (p.1 == g) with _ | _
    · rfl
    · exfalso
      have hp_full : p ∈ decls.pairs.toList := by
        rw [hsplit]; exact List.mem_append_left _ hp
      have hp_eq := hunique p hp_full hbeq
      have hp_in_pre : (g, Typed.Declaration.constructor td_dt td_c) ∈ pre := hp_eq ▸ hp
      obtain ⟨i, hi_lt, hi_eq⟩ := List.getElem_of_mem hp_in_pre
      have hi_lt_full : i < decls.pairs.toList.length := by
        rw [hsplit, List.length_append]
        exact Nat.lt_add_right _ hi_lt
      have hmid_lt_full : pre.length < decls.pairs.toList.length := by
        rw [hsplit, List.length_append]
        exact Nat.lt_add_of_pos_right (Nat.zero_lt_succ _)
      have hlist_i : decls.pairs.toList[i]'hi_lt_full =
          (g, Typed.Declaration.constructor td_dt td_c) := by
        rw [show decls.pairs.toList[i]'hi_lt_full =
            (pre ++ (g, Typed.Declaration.constructor td_dt td_c) :: post)[i]'(by
              rw [List.length_append]; exact Nat.lt_add_right _ hi_lt) from by
          congr 1 <;> exact hsplit]
        rw [List.getElem_append_left hi_lt]; exact hi_eq
      have hlist_mid : decls.pairs.toList[pre.length]'hmid_lt_full =
          (g, Typed.Declaration.constructor td_dt td_c) := by
        rw [show decls.pairs.toList[pre.length]'hmid_lt_full =
            (pre ++ (g, Typed.Declaration.constructor td_dt td_c) :: post)[pre.length]'(by
              rw [List.length_append]
              exact Nat.lt_add_of_pos_right (Nat.zero_lt_succ _)) from by
          congr 1 <;> exact hsplit]
        rw [List.getElem_append_right (Nat.le_refl _)]
        simp
      have hkey_eq : ((decls.pairs.toList[i]'hi_lt_full).1 ==
          (decls.pairs.toList[pre.length]'hmid_lt_full).1) = true := by
        rw [hlist_i, hlist_mid]; simp
      have hij := indexMap_pairs_index_unique_of_key decls hi_lt_full hmid_lt_full hkey_eq
      omega
  have hno_g_post : ∀ p ∈ post, (p.1 == g) = false := by
    intro p hp
    rcases hbeq : (p.1 == g) with _ | _
    · rfl
    · exfalso
      have hp_full : p ∈ decls.pairs.toList := by
        rw [hsplit]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hp)
      have hp_eq := hunique p hp_full hbeq
      have hp_in_post : (g, Typed.Declaration.constructor td_dt td_c) ∈ post := hp_eq ▸ hp
      obtain ⟨i, hi_lt, hi_eq⟩ := List.getElem_of_mem hp_in_post
      have hipost_lt_full : pre.length + (i + 1) < decls.pairs.toList.length := by
        rw [hsplit, List.length_append]; simp [List.length_cons]; omega
      have hmid_lt_full : pre.length < decls.pairs.toList.length := by
        rw [hsplit, List.length_append]
        exact Nat.lt_add_of_pos_right (Nat.zero_lt_succ _)
      have hlist_ipost : decls.pairs.toList[pre.length + (i + 1)]'hipost_lt_full =
          (g, Typed.Declaration.constructor td_dt td_c) := by
        rw [show decls.pairs.toList[pre.length + (i + 1)]'hipost_lt_full =
            (pre ++ (g, Typed.Declaration.constructor td_dt td_c) :: post)[pre.length + (i + 1)]'(by
              rw [List.length_append]; simp [List.length_cons]; omega) from by
          congr 1 <;> exact hsplit]
        rw [List.getElem_append_right (by omega : pre.length ≤ pre.length + (i + 1))]
        simp
        exact hi_eq
      have hlist_mid : decls.pairs.toList[pre.length]'hmid_lt_full =
          (g, Typed.Declaration.constructor td_dt td_c) := by
        rw [show decls.pairs.toList[pre.length]'hmid_lt_full =
            (pre ++ (g, Typed.Declaration.constructor td_dt td_c) :: post)[pre.length]'(by
              rw [List.length_append]
              exact Nat.lt_add_of_pos_right (Nat.zero_lt_succ _)) from by
          congr 1 <;> exact hsplit]
        rw [List.getElem_append_right (Nat.le_refl _)]
        simp
      have hkey_eq : ((decls.pairs.toList[pre.length + (i + 1)]'hipost_lt_full).1 ==
          (decls.pairs.toList[pre.length]'hmid_lt_full).1) = true := by
        rw [hlist_ipost, hlist_mid]; simp
      have hij := indexMap_pairs_index_unique_of_key decls hipost_lt_full hmid_lt_full hkey_eq
      omega
  rw [hsplit]
  rw [List.foldl_append]
  rw [List.foldl_cons]
  rw [srcStep_foldl_no_g_preserves decls mono post _ hno_g_post]
  exact srcStep_at_g_inserts_ctor_explicit decls mono
    (List.foldl (srcStep decls mono) default pre) hdt_params (g := g)
    (td_dt := td_dt) (td_c := td_c)

/-- `dtStep` foldl preserves an *exact* value at `g` under both
`hDtNotKey` (no outer dt-insert overrides) and `hCtorNotKey` (no inner
ctor-fold insert overrides). Reduces to `dtStep_foldl_no_g_preserves` (which
already has the correct hypothesis pattern). -/
private theorem dtStep_foldl_preserves_explicit_at_g
    (mono : MonoMap) (newDataTypes : Array DataType)
    {g : Global} {dummy : Typed.Declaration}
    (init : Typed.Decls)
    (hinit : init.getByKey g = some dummy)
    (hDtNotKey : ∀ dt ∈ newDataTypes, dt.name ≠ g)
    (hCtorNotKey : ∀ dt ∈ newDataTypes, ∀ c ∈ dt.constructors,
      dt.name.pushNamespace c.nameHead ≠ g) :
    (newDataTypes.foldl (dtStep mono) init).getByKey g = some dummy := by
  rw [← Array.foldl_toList]
  have hno_dt_list : ∀ dt ∈ newDataTypes.toList, dt.name ≠ g := by
    intro dt hdt; exact hDtNotKey dt (Array.mem_toList_iff.mp hdt)
  have hno_ctor_list : ∀ dt ∈ newDataTypes.toList, ∀ c ∈ dt.constructors,
      dt.name.pushNamespace c.nameHead ≠ g := by
    intro dt hdt c hc; exact hCtorNotKey dt (Array.mem_toList_iff.mp hdt) c hc
  rw [dtStep_foldl_no_g_preserves mono newDataTypes.toList init hno_dt_list hno_ctor_list]
  exact hinit

/-- `fnStep` foldl preserves an *exact* value at `g` under `hFnNotKey`. -/
private theorem fnStep_foldl_preserves_explicit_at_g
    (decls : Typed.Decls) (mono : MonoMap) (newFunctions : Array Typed.Function)
    {g : Global} {dummy : Typed.Declaration}
    (init : Typed.Decls)
    (hinit : init.getByKey g = some dummy)
    (hFnNotKey : ∀ f ∈ newFunctions, f.name ≠ g) :
    (newFunctions.foldl (fnStep decls mono) init).getByKey g = some dummy := by
  rw [← Array.foldl_toList]
  have hno_fn_list : ∀ f ∈ newFunctions.toList, f.name ≠ g := by
    intro f hf; exact hFnNotKey f (Array.mem_toList_iff.mp hf)
  rw [fnStep_foldl_no_g_preserves decls mono newFunctions.toList init hno_fn_list]
  exact hinit

/-- Explicit-structure version of `concretizeBuild_preserves_ctor_kind_fwd`:
under the disjointness hypotheses + typed `.ctor` at g, mono `.ctor` at g
has SPECIFIC structure derivable from typed dt + ctor via empty-subst rewriteTyp. -/
private theorem concretizeBuild_at_typed_ctor_explicit
    (typedDecls : Typed.Decls) (mono : MonoMap)
    (newFunctions : Array Typed.Function) (newDataTypes : Array DataType)
    {g : Global} {td_dt : DataType} {td_c : Constructor}
    (hget : typedDecls.getByKey g = some (.constructor td_dt td_c))
    (hdt_params : td_dt.params = [])
    (hDtNotKey : ∀ dt ∈ newDataTypes, dt.name ≠ g)
    (hFnNotKey : ∀ f ∈ newFunctions, f.name ≠ g)
    (hCtorNotKey : ∀ dt ∈ newDataTypes, ∀ c ∈ dt.constructors,
      dt.name.pushNamespace c.nameHead ≠ g) :
    let emptySubst : Global → Option Typ := fun _ => none
    let rewrittenCtors := td_dt.constructors.map fun c =>
      { c with argTypes := c.argTypes.map (rewriteTyp emptySubst mono) }
    let monoDt : DataType := { td_dt with constructors := rewrittenCtors }
    let monoC : Constructor :=
      { td_c with argTypes := td_c.argTypes.map (rewriteTyp emptySubst mono) }
    (concretizeBuild typedDecls mono newFunctions newDataTypes).getByKey g =
      some (.constructor monoDt monoC) := by
  rw [concretizeBuild_eq]
  have h1 := fromSource_inserts_ctor_at_key_explicit typedDecls mono hget hdt_params
  have h2 := dtStep_foldl_preserves_explicit_at_g mono newDataTypes _ h1
    hDtNotKey hCtorNotKey
  exact fnStep_foldl_preserves_explicit_at_g typedDecls mono newFunctions _ h2 hFnNotKey

/-! #### Generalized explicit-structure under FullyMono + StrongNewNameShape.

`concretizeBuild_at_typed_ctor_explicit` requires `hCtorNotKey` (no origin 4
fires at `g`). Under `FullyMono` + `StrongNewNameShape`, origin 4 IS possible
(drain pushes a `newDt` for `td_dt` since `td_dt.params = []` ⇒ the args=#[]
self-instantiation is registered, and `withNewDts`'s ctor-fold inserts at
`td_dt.name.pushNamespace td_c.nameHead = g` overriding `fromSource`).

The KEY INSIGHT: under `StrongNewNameShape`, every `dt' ∈ drained.newDataTypes`
has constructors whose `nameHead`s match its source-typed origin's
constructors `nameHead`s positionally. For a `dt'` whose `pushNamespace`
matches `g`, injectivity of `pushNamespace` plus `Typed.Decls.CtorIsKey`
(which gives `g = td_dt.name.pushNamespace td_c.nameHead`) plus IndexMap key
uniqueness identify the source origin as `td_dt`. So the override at `g`
yields a `monoDt` whose `nameHead`-positional structure agrees with `td_dt`,
and a `monoC` with `nameHead = td_c.nameHead`. -/

/-- Structural predicate: a typed declaration at `g` is a `.constructor`
whose datatype `nameHead`-structure matches `td_dt` positionally and whose
constructor `nameHead` equals `td_c.nameHead`. The "general" target shape
satisfied by both `fromSource`'s Case-A output (rewritten `td_dt`) and
`withNewDts`'s Case-B override (rewritten `dt'` with `dt'`'s nameHeads
matching `td_dt`'s by `StrongNewNameShape`). -/
private def MatchesTdShape (td_dt : DataType) (td_c : Constructor)
    (d : Typed.Declaration) : Prop :=
  ∃ md_dt md_c, d = .constructor md_dt md_c ∧
    md_dt.constructors.length = td_dt.constructors.length ∧
    md_c.nameHead = td_c.nameHead ∧
    (∀ i (hi : i < td_dt.constructors.length),
      ∃ hi' : i < md_dt.constructors.length,
      (md_dt.constructors[i]'hi').nameHead = (td_dt.constructors[i]'hi).nameHead) ∧
    -- Positional structural equality at td_c's position. At any position i
    -- where td_dt[i] = td_c, md_dt[i] structurally equals md_c.
    (∀ i (hi : i < td_dt.constructors.length),
      (td_dt.constructors[i]'hi) = td_c → ∃ hi' : i < md_dt.constructors.length,
      (md_dt.constructors[i]'hi') = md_c)

/-- The Case-A explicit value (rewritten `td_dt`, rewritten `td_c`) satisfies
`MatchesTdShape`. `rewriteTyp` only touches `argTypes`, leaving `nameHead`
intact, so length and positional `nameHead`s are preserved by the inner map. -/
private theorem MatchesTdShape_caseA
    (mono : MonoMap) (td_dt : DataType) (td_c : Constructor) :
    let emptySubst : Global → Option Typ := fun _ => none
    let rewrittenCtors := td_dt.constructors.map fun c' =>
      { c' with argTypes := c'.argTypes.map (rewriteTyp emptySubst mono) }
    let monoDt : DataType := { td_dt with constructors := rewrittenCtors }
    let monoC : Constructor :=
      { td_c with argTypes := td_c.argTypes.map (rewriteTyp emptySubst mono) }
    MatchesTdShape td_dt td_c (.constructor monoDt monoC) := by
  refine ⟨_, _, rfl, ?_, rfl, ?_, ?_⟩
  · simp only [List.length_map]
  · intro i hi
    have hi' : i < td_dt.constructors.length := hi
    refine ⟨by simp only [List.length_map]; exact hi', ?_⟩
    simp only [List.getElem_map]
  · intro i hi heq
    refine ⟨by simp only [List.length_map]; exact hi, ?_⟩
    simp only [List.getElem_map]
    rw [heq]

/-- Inner ctor fold preserves `MatchesTdShape`. Either the inner insert at
`dt'.name.pushNamespace c.nameHead` doesn't hit `g` (preserving the inductive
value), or it does — at which point we must build a `MatchesTdShape` witness
for `(.constructor newDt' c)`. The build-witness function `hWit` is supplied
externally: it produces the `MatchesTdShape` package whenever a constructor's
pushed-key matches `g`. -/
private theorem dtCtorFold_preserves_MatchesTdShape
    (dt' : DataType) (newDt' : DataType)
    {g : Global} {td_dt : DataType} {td_c : Constructor}
    (cs : List Constructor)
    (hWit : ∀ c ∈ cs, dt'.name.pushNamespace c.nameHead = g →
      MatchesTdShape td_dt td_c (.constructor newDt' c))
    (acc : Typed.Decls)
    (hacc : ∃ d, acc.getByKey g = some d ∧ MatchesTdShape td_dt td_c d) :
    ∃ d, (cs.foldl
        (fun acc'' c =>
          let cName := dt'.name.pushNamespace c.nameHead
          acc''.insert cName (.constructor newDt' c))
        acc).getByKey g = some d ∧ MatchesTdShape td_dt td_c d := by
  induction cs generalizing acc with
  | nil => exact hacc
  | cons c rest ih =>
    simp only [List.foldl_cons]
    apply ih (fun c' hc' => hWit c' (List.mem_cons_of_mem _ hc'))
    by_cases hbeq : (dt'.name.pushNamespace c.nameHead == g) = true
    · have heq : dt'.name.pushNamespace c.nameHead = g := LawfulBEq.eq_of_beq hbeq
      refine ⟨.constructor newDt' c, ?_, hWit c List.mem_cons_self heq⟩
      show ((acc.insert (dt'.name.pushNamespace c.nameHead)
        (.constructor newDt' c)).getByKey g) = some (.constructor newDt' c)
      rw [heq]; exact IndexMap.getByKey_insert_self _ _ _
    · have hne : (dt'.name.pushNamespace c.nameHead == g) = false :=
        Bool.not_eq_true _ |>.mp hbeq
      obtain ⟨d, hget, hM⟩ := hacc
      refine ⟨d, ?_, hM⟩
      show ((acc.insert (dt'.name.pushNamespace c.nameHead)
        (.constructor newDt' c)).getByKey g) = some d
      rw [IndexMap.getByKey_insert_of_beq_false _ _ hne]; exact hget

/-- Single dtStep preserves `MatchesTdShape` at `g` under `dt'.name ≠ g`
(outer dt-insert doesn't touch g) plus a per-`dt'` post-rewrite witness
builder. The builder takes a (post-rewrite) constructor `c` whose pushed-key
matches `g` and produces the `MatchesTdShape` package. Caller phrases the
witness in terms of the rewritten `newDt'` (via the same let-binding here) so
it lines up with what the inner ctor-fold actually inserts. -/
private theorem dtStep_preserves_MatchesTdShape
    (mono : MonoMap) (acc : Typed.Decls) (dt' : DataType)
    {g : Global} {td_dt : DataType} {td_c : Constructor}
    (hdt_ne : dt'.name ≠ g)
    (hWit : ∀ c ∈ dt'.constructors.map (fun c' =>
        { c' with argTypes := c'.argTypes.map (rewriteTyp (fun _ => none) mono) }),
      dt'.name.pushNamespace c.nameHead = g →
      MatchesTdShape td_dt td_c (.constructor
        { dt' with constructors := dt'.constructors.map (fun c' =>
          { c' with argTypes := c'.argTypes.map (rewriteTyp (fun _ => none) mono) }) } c))
    (hacc : ∃ d, acc.getByKey g = some d ∧ MatchesTdShape td_dt td_c d) :
    ∃ d, (dtStep mono acc dt').getByKey g = some d ∧
      MatchesTdShape td_dt td_c d := by
  unfold dtStep
  have hbeq_dt_name : (dt'.name == g) = false := by
    rw [beq_eq_false_iff_ne]; exact hdt_ne
  let emptySubst : Global → Option Typ := fun _ => none
  let rewrittenCtors := dt'.constructors.map fun c =>
    { c with argTypes := c.argTypes.map (rewriteTyp emptySubst mono) }
  let newDt' : DataType := { dt' with constructors := rewrittenCtors }
  -- After outer dt-insert: still has same shape at g.
  have hacc' : ∃ d, (acc.insert dt'.name (Typed.Declaration.dataType newDt')).getByKey g
      = some d ∧ MatchesTdShape td_dt td_c d := by
    obtain ⟨d, hget, hM⟩ := hacc
    refine ⟨d, ?_, hM⟩
    rw [IndexMap.getByKey_insert_of_beq_false _ _ hbeq_dt_name]; exact hget
  exact dtCtorFold_preserves_MatchesTdShape dt' newDt'
    rewrittenCtors hWit _ hacc'

/-- fnStep preserves `MatchesTdShape` at `g` under `f.name ≠ g`. -/
private theorem fnStep_preserves_MatchesTdShape
    (decls : Typed.Decls) (mono : MonoMap) (acc : Typed.Decls) (f : Typed.Function)
    {g : Global} {td_dt : DataType} {td_c : Constructor}
    (hfn_ne : f.name ≠ g)
    (hacc : ∃ d, acc.getByKey g = some d ∧ MatchesTdShape td_dt td_c d) :
    ∃ d, (fnStep decls mono acc f).getByKey g = some d ∧
      MatchesTdShape td_dt td_c d := by
  unfold fnStep
  have hbeq : (f.name == g) = false := by
    rw [beq_eq_false_iff_ne]; exact hfn_ne
  obtain ⟨d, hget, hM⟩ := hacc
  refine ⟨d, ?_, hM⟩
  rw [IndexMap.getByKey_insert_of_beq_false _ _ hbeq]; exact hget

/-- **Generalized explicit-structure**: under `FullyMono` + `StrongNewNameShape`
on drained, the `concretizeBuild` result at `g` (where `typedDecls` has
`.constructor td_dt td_c`) carries the same `nameHead`-positional structure as
`td_dt` + `td_c`, *even when origin 4 fires* (i.e., `withNewDts` overrides at
`g`).

Note on signature: the spec strategy needs the typed-side fact
`g = td_dt.name.pushNamespace td_c.nameHead` to bridge origin 4 back to
`td_dt`. This is supplied via the `Typed.Decls.CtorIsKey typedDecls`
hypothesis (a structural invariant of `checkAndSimplify`'s output, derivable
at the call site via `checkAndSimplify_preserves_ctorIsKey` / equivalent —
already proven for the `Typed.Decls.CtorIsKey` predicate downstream). -/
private theorem concretizeBuild_at_typed_ctor_explicit_general
    (typedDecls : Typed.Decls) (drained : DrainState)
    (hStrong : drained.StrongNewNameShape typedDecls)
    (hfn_params_empty : ∀ k f,
      typedDecls.getByKey k = some (.function f) → f.params = [])
    (hdt_params_empty : ∀ k dt,
      typedDecls.getByKey k = some (.dataType dt) → dt.params = [])
    {g : Global} {td_dt : DataType} {td_c : Constructor}
    (hg_pushed : g = td_dt.name.pushNamespace td_c.nameHead)
    (hget : typedDecls.getByKey g = some (.constructor td_dt td_c))
    (hdt_companion : typedDecls.getByKey td_dt.name = some (.dataType td_dt))
    (_hc_mem : td_c ∈ td_dt.constructors)
    (hdt_distinct : ∀ i j (hi : i < td_dt.constructors.length)
                              (hj : j < td_dt.constructors.length),
        (td_dt.constructors[i]'hi).nameHead = (td_dt.constructors[j]'hj).nameHead → i = j) :
    ∃ md_dt md_c,
      (concretizeBuild typedDecls drained.mono drained.newFunctions
          drained.newDataTypes).getByKey g = some (.constructor md_dt md_c) ∧
      md_dt.constructors.length = td_dt.constructors.length ∧
      md_c.nameHead = td_c.nameHead ∧
      (∀ i (hi : i < td_dt.constructors.length),
        ∃ hi' : i < md_dt.constructors.length,
        (md_dt.constructors[i]'hi').nameHead = (td_dt.constructors[i]'hi).nameHead) ∧
      -- Positional structural equality at td_c's position.
      (∀ i (hi : i < td_dt.constructors.length),
        (td_dt.constructors[i]'hi) = td_c → ∃ hi' : i < md_dt.constructors.length,
        (md_dt.constructors[i]'hi') = md_c) := by
  -- `td_dt.params = []` (FullyMono).
  have hdt_params : td_dt.params = [] := hdt_params_empty td_dt.name td_dt hdt_companion
  -- Disjointness for newDataTypes (outer dt-key ≠ g).
  have hDtNotKey : ∀ dt' ∈ drained.newDataTypes, dt'.name ≠ g := by
    intro dt' hmem heq
    obtain ⟨g_orig, args, dt_orig, hname, hget_orig, hargs_sz, _⟩ :=
      hStrong.2 dt' hmem
    have hdt_orig_params := hdt_params_empty g_orig dt_orig hget_orig
    have hargs_zero : args.size = 0 := by rw [hargs_sz, hdt_orig_params]; rfl
    have hargs_empty : args = #[] := Array.size_eq_zero_iff.mp hargs_zero
    have hname_eq : dt'.name = g_orig := by
      rw [hname, hargs_empty]; exact concretizeName_empty_args g_orig
    rw [hname_eq] at heq
    rw [heq] at hget_orig
    rw [hget] at hget_orig
    cases hget_orig
  -- Disjointness for newFunctions.
  have hFnNotKey : ∀ f ∈ drained.newFunctions, f.name ≠ g := by
    intro f hmem heq
    obtain ⟨g_orig, args, f_orig, hname, hget_orig, hargs_sz⟩ :=
      hStrong.1 f hmem
    have hf_orig_params := hfn_params_empty g_orig f_orig hget_orig
    have hargs_zero : args.size = 0 := by rw [hargs_sz, hf_orig_params]; rfl
    have hargs_empty : args = #[] := Array.size_eq_zero_iff.mp hargs_zero
    have hname_eq : f.name = g_orig := by
      rw [hname, hargs_empty]; exact concretizeName_empty_args g_orig
    rw [hname_eq] at heq
    rw [heq] at hget_orig
    rw [hget] at hget_orig
    cases hget_orig
  -- Per-`dt' ∈ drained.newDataTypes` post-rewrite witness builder. When dt'
  -- writes at g (i.e., `dt'.name.pushNamespace c.nameHead = g` for some c),
  -- the prefix injection forces `dt'.name = td_dt.name`, so by IndexMap key
  -- uniqueness `dt_orig = td_dt`, and `dt'.constructors.map nameHead =
  -- td_dt.constructors.map nameHead`. Combined with `c.nameHead = td_c.nameHead`
  -- (from suffix injection), the rewritten newDt' + c produces the desired
  -- `MatchesTdShape` package. When dt' does NOT write at g, the witness is
  -- vacuous (premise unsatisfiable).
  have hPerDtWit : ∀ dt' ∈ drained.newDataTypes,
      ∀ c ∈ dt'.constructors.map (fun c' =>
          { c' with argTypes := c'.argTypes.map (rewriteTyp (fun _ => none) drained.mono) }),
      dt'.name.pushNamespace c.nameHead = g →
        MatchesTdShape td_dt td_c (.constructor
          { dt' with constructors := dt'.constructors.map (fun c' =>
            { c' with argTypes := c'.argTypes.map (rewriteTyp (fun _ => none) drained.mono) }) } c) := by
    intro dt' hmem c hcmem hpush
    -- Suffix + prefix injectivity from pushed-key equality.
    rw [hg_pushed] at hpush
    -- hpush : dt'.name.pushNamespace c.nameHead = td_dt.name.pushNamespace td_c.nameHead
    have h_name_eq : Lean.Name.str dt'.name.toName c.nameHead =
        Lean.Name.str td_dt.name.toName td_c.nameHead := by
      have := hpush
      unfold Global.pushNamespace at this
      exact Global.mk.inj this
    have hToName : dt'.name.toName = td_dt.name.toName := by injection h_name_eq
    have hSuffix : c.nameHead = td_c.nameHead := by injection h_name_eq
    have hdt_name_eq : dt'.name = td_dt.name := by
      cases hd : dt'.name; cases hT : td_dt.name
      rw [hd, hT] at hToName
      simp only [Global.toName] at hToName
      congr 1
    -- StrongNewNameShape on dt': nameHead-positional correspondence to dt_orig.
    obtain ⟨g_orig, args, dt_orig, hname, hget_orig, hargs_sz, hctors_nh⟩ :=
      hStrong.2 dt' hmem
    have hdt_orig_params := hdt_params_empty g_orig dt_orig hget_orig
    have hargs_zero : args.size = 0 := by rw [hargs_sz, hdt_orig_params]; rfl
    have hargs_empty : args = #[] := Array.size_eq_zero_iff.mp hargs_zero
    have hgorig_pre : dt'.name = g_orig := by
      rw [hname, hargs_empty]; exact concretizeName_empty_args g_orig
    have hgorig_eq : g_orig = td_dt.name := by rw [← hgorig_pre]; exact hdt_name_eq
    have hdt_orig_eq : dt_orig = td_dt := by
      rw [hgorig_eq] at hget_orig
      rw [hdt_companion] at hget_orig
      cases hget_orig; rfl
    rw [hdt_orig_eq] at hctors_nh
    -- hctors_nh : dt'.constructors.map nameHead = td_dt.constructors.map nameHead.
    have hLen : dt'.constructors.length = td_dt.constructors.length := by
      have := congrArg List.length hctors_nh
      simp [List.length_map] at this
      exact this
    -- Per-position nameHead correspondence between dt'.constructors and
    -- td_dt.constructors (used for both MatchesTdShape clauses below).
    have hPosNH : ∀ i (hi : i < td_dt.constructors.length),
        ∃ hi' : i < dt'.constructors.length,
        (dt'.constructors[i]'hi').nameHead = (td_dt.constructors[i]'hi).nameHead := by
      intro i hi
      have hi' : i < dt'.constructors.length := by rw [hLen]; exact hi
      refine ⟨hi', ?_⟩
      have hi_dt : i < (dt'.constructors.map (·.nameHead)).length := by
        rw [List.length_map]; exact hi'
      have hi_td : i < (td_dt.constructors.map (·.nameHead)).length := by
        rw [List.length_map]; exact hi
      have h_nh :
          (dt'.constructors.map (·.nameHead))[i]'hi_dt =
          (td_dt.constructors.map (·.nameHead))[i]'hi_td := by
        congr 1
      rw [List.getElem_map, List.getElem_map] at h_nh
      exact h_nh
    -- Now build MatchesTdShape for `(.constructor newDt' c)` where `newDt'` =
    -- `{ dt' with constructors := rewrittenCtors }` and rewrittenCtors length =
    -- dt'.constructors.length.
    refine ⟨_, c, rfl, ?_, hSuffix, ?_, ?_⟩
    · simp only [List.length_map]; exact hLen
    · intro i hi
      have hi' : i < dt'.constructors.length := by rw [hLen]; exact hi
      refine ⟨by simp only [List.length_map]; exact hi', ?_⟩
      simp only [List.getElem_map]
      exact (hPosNH i hi).2
    · -- Positional structural equality at td_c's position.
      -- Strategy: `c ∈ rewrittenCtors`, so `c = rewrittenCtors[k]` for some k.
      -- `c.nameHead = td_c.nameHead = td_dt[i].nameHead` (via heq).
      -- `rewrittenCtors[k].nameHead = dt'[k].nameHead = td_dt[k].nameHead`
      -- (via hctors_nh). By distinctness on td_dt nameHeads, k = i.
      -- So `rewrittenCtors[i] = c`, hence `newDt'.constructors[i] = c = md_c`.
      intro i hi heq
      have hi'_dt' : i < dt'.constructors.length := by rw [hLen]; exact hi
      have hi'_new : i < (dt'.constructors.map (fun c' =>
          { c' with argTypes := c'.argTypes.map (rewriteTyp (fun _ => none)
            drained.mono) })).length := by simp only [List.length_map]; exact hi'_dt'
      refine ⟨hi'_new, ?_⟩
      -- Identify k from c ∈ rewrittenCtors.
      obtain ⟨k, hk_lt, hk_eq⟩ := List.getElem_of_mem hcmem
      have hk_lt_dt' : k < dt'.constructors.length := by
        simp only [List.length_map] at hk_lt; exact hk_lt
      -- c.nameHead = rewrittenCtors[k].nameHead = dt'.constructors[k].nameHead.
      have hk_nh_c : c.nameHead = (dt'.constructors[k]'hk_lt_dt').nameHead := by
        rw [← hk_eq]; simp only [List.getElem_map]
      -- dt'.constructors[k].nameHead = td_dt.constructors[k].nameHead via hctors_nh.
      have hk_lt_td : k < td_dt.constructors.length := by rw [← hLen]; exact hk_lt_dt'
      have hk_nh_td : (dt'.constructors[k]'hk_lt_dt').nameHead =
          (td_dt.constructors[k]'hk_lt_td).nameHead := (hPosNH k hk_lt_td).2
      -- Combine: c.nameHead = td_dt[k].nameHead. And c.nameHead = td_c.nameHead.
      -- And td_dt[i] = td_c (by heq) so td_dt[i].nameHead = td_c.nameHead.
      have hk_eq_i : k = i := by
        apply hdt_distinct k i hk_lt_td hi
        -- Goal: td_dt[k].nameHead = td_dt[i].nameHead.
        rw [← hk_nh_td, ← hk_nh_c, hSuffix, ← heq]
      subst hk_eq_i
      -- Now newDt'.constructors[i] = rewrittenCtors[i] = c.
      have hgoal : (dt'.constructors.map (fun c' =>
          { c' with argTypes := c'.argTypes.map (rewriteTyp (fun _ => none)
            drained.mono) }))[k]'hk_lt = c := hk_eq
      exact hgoal
  -- Compose: starting from fromSource's Case-A explicit value, dtStep fold
  -- preserves `MatchesTdShape` (per-dt' via hPerDtWit), then fnStep fold
  -- preserves it (under hFnNotKey).
  rw [concretizeBuild_eq]
  -- Step 1: fromSource produces Case-A `MatchesTdShape`.
  have h0 : ∃ d, (typedDecls.pairs.foldl (srcStep typedDecls drained.mono) default).getByKey g
      = some d ∧ MatchesTdShape td_dt td_c d := by
    have h := fromSource_inserts_ctor_at_key_explicit typedDecls drained.mono hget hdt_params
    refine ⟨_, h, ?_⟩
    exact MatchesTdShape_caseA drained.mono td_dt td_c
  -- Step 2: dtStep foldl preserves it.
  have h1 : ∃ d, (drained.newDataTypes.foldl (dtStep drained.mono)
      (typedDecls.pairs.foldl (srcStep typedDecls drained.mono) default)).getByKey g
      = some d ∧ MatchesTdShape td_dt td_c d := by
    apply Array.foldl_induction
      (motive := fun (_ : Nat) (acc : Typed.Decls) =>
        ∃ d, acc.getByKey g = some d ∧ MatchesTdShape td_dt td_c d) h0
    intro i acc hinv
    have hdt_mem : drained.newDataTypes[i.val]'i.isLt ∈ drained.newDataTypes :=
      Array.getElem_mem _
    have hdt_ne := hDtNotKey _ hdt_mem
    have hWit_i := hPerDtWit _ hdt_mem
    exact dtStep_preserves_MatchesTdShape drained.mono acc _ hdt_ne hWit_i hinv
  -- Step 3: fnStep foldl preserves it.
  have h2 : ∃ d, (drained.newFunctions.foldl (fnStep typedDecls drained.mono)
      (drained.newDataTypes.foldl (dtStep drained.mono)
        (typedDecls.pairs.foldl (srcStep typedDecls drained.mono) default))).getByKey g
      = some d ∧ MatchesTdShape td_dt td_c d := by
    apply Array.foldl_induction
      (motive := fun (_ : Nat) (acc : Typed.Decls) =>
        ∃ d, acc.getByKey g = some d ∧ MatchesTdShape td_dt td_c d) h1
    intro i acc hinv
    have hf_mem : drained.newFunctions[i.val]'i.isLt ∈ drained.newFunctions :=
      Array.getElem_mem _
    have hf_ne := hFnNotKey _ hf_mem
    exact fnStep_preserves_MatchesTdShape typedDecls drained.mono acc _ hf_ne hinv
  -- Unpack the final `MatchesTdShape` into the goal's existential structure.
  obtain ⟨d, hd, ⟨md_dt, md_c, hd_eq, hLen, hNH, hPos, hStruct⟩⟩ := h2
  rw [hd_eq] at hd
  exact ⟨md_dt, md_c, hd, hLen, hNH, hPos, hStruct⟩

/-! #### Phase A.2 — typed↔monoDecls dataType kind correspondence (forward).

Mirrors the ctor variant. For source/typed `.dataType` at `g`:
* `fromSource` fold processes the unique `(g, .dataType td_dt)` pair under
  `td_dt.params = []`, inserting `.dataType` at `g`.
* `withNewDts` fold inserts `.dataType` at `dt'.name` and `.constructor` at
  each `dt'.name.pushNamespace c.nameHead`. The `dt'.name = g` case re-inserts
  `.dataType` (kind preserved); under `hDtCtorNotKey`, no inner ctor key
  equals `g`.
* `newFunctions` fold inserts `.function` at `f.name`. Under `hFnNotKey`,
  no insertion at `g`.
-/

/-- A single step of `srcStep` on the target `(g, .dataType td_dt)` pair
under `td_dt.params = []` produces a `.dataType` entry at `g`. -/
private theorem srcStep_at_g_inserts_dataType
    (decls : Typed.Decls) (mono : MonoMap) (acc : Typed.Decls)
    {g : Global} {td_dt : DataType}
    (hdt_params : td_dt.params = []) :
    ∃ md_dt,
      (srcStep decls mono acc (g, .dataType td_dt)).getByKey g =
        some (.dataType md_dt) := by
  unfold srcStep
  have hp : td_dt.params.isEmpty = true := by rw [hdt_params]; rfl
  let emptySubst : Global → Option Typ := fun _ => none
  let newDt : DataType := { td_dt with
    constructors := td_dt.constructors.map fun c =>
      { c with argTypes := c.argTypes.map (rewriteTyp emptySubst mono) } }
  simp only [hp, if_true]
  exact ⟨newDt, IndexMap.getByKey_insert_self _ _ _⟩

/-- `fromSource` fold inserts `.dataType` at `g` when source has `.dataType`
at `g`. -/
private theorem fromSource_inserts_dataType_at_key
    (decls : Typed.Decls) (mono : MonoMap)
    {g : Global} {td_dt : DataType}
    (hget : decls.getByKey g = some (.dataType td_dt))
    (hdt_params : td_dt.params = []) :
    ∃ md_dt,
      (decls.pairs.foldl (srcStep decls mono) default).getByKey g =
        some (.dataType md_dt) := by
  rw [← Array.foldl_toList]
  have hmem : (g, Typed.Declaration.dataType td_dt) ∈ decls.pairs.toList :=
    IndexMap.mem_pairs_of_getByKey _ _ _ hget
  have hunique : ∀ p ∈ decls.pairs.toList,
      (p.1 == g) = true → p = (g, Typed.Declaration.dataType td_dt) := by
    intro p hp hpkey
    exact indexMap_pairs_key_unique _ hp hmem hpkey
  obtain ⟨pre, post, hsplit⟩ := List.append_of_mem hmem
  have hno_g_pre : ∀ p ∈ pre, (p.1 == g) = false := by
    intro p hp
    rcases hbeq : (p.1 == g) with _ | _
    · rfl
    · exfalso
      have hp_full : p ∈ decls.pairs.toList := by
        rw [hsplit]; exact List.mem_append_left _ hp
      have hp_eq := hunique p hp_full hbeq
      have hp_in_pre : (g, Typed.Declaration.dataType td_dt) ∈ pre := hp_eq ▸ hp
      obtain ⟨i, hi_lt, hi_eq⟩ := List.getElem_of_mem hp_in_pre
      have hi_lt_full : i < decls.pairs.toList.length := by
        rw [hsplit, List.length_append]
        exact Nat.lt_add_right _ hi_lt
      have hmid_lt_full : pre.length < decls.pairs.toList.length := by
        rw [hsplit, List.length_append]
        exact Nat.lt_add_of_pos_right (Nat.zero_lt_succ _)
      have hlist_i : decls.pairs.toList[i]'hi_lt_full =
          (g, Typed.Declaration.dataType td_dt) := by
        rw [show decls.pairs.toList[i]'hi_lt_full =
            (pre ++ (g, Typed.Declaration.dataType td_dt) :: post)[i]'(by
              rw [List.length_append]; exact Nat.lt_add_right _ hi_lt) from by
          congr 1 <;> exact hsplit]
        rw [List.getElem_append_left hi_lt]; exact hi_eq
      have hlist_mid : decls.pairs.toList[pre.length]'hmid_lt_full =
          (g, Typed.Declaration.dataType td_dt) := by
        rw [show decls.pairs.toList[pre.length]'hmid_lt_full =
            (pre ++ (g, Typed.Declaration.dataType td_dt) :: post)[pre.length]'(by
              rw [List.length_append]
              exact Nat.lt_add_of_pos_right (Nat.zero_lt_succ _)) from by
          congr 1 <;> exact hsplit]
        rw [List.getElem_append_right (Nat.le_refl _)]
        simp
      have hkey_eq : ((decls.pairs.toList[i]'hi_lt_full).1 ==
          (decls.pairs.toList[pre.length]'hmid_lt_full).1) = true := by
        rw [hlist_i, hlist_mid]; simp
      have hij := indexMap_pairs_index_unique_of_key decls hi_lt_full hmid_lt_full hkey_eq
      omega
  have hno_g_post : ∀ p ∈ post, (p.1 == g) = false := by
    intro p hp
    rcases hbeq : (p.1 == g) with _ | _
    · rfl
    · exfalso
      have hp_full : p ∈ decls.pairs.toList := by
        rw [hsplit]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hp)
      have hp_eq := hunique p hp_full hbeq
      have hp_in_post : (g, Typed.Declaration.dataType td_dt) ∈ post := hp_eq ▸ hp
      obtain ⟨i, hi_lt, hi_eq⟩ := List.getElem_of_mem hp_in_post
      have hipost_lt_full : pre.length + (i + 1) < decls.pairs.toList.length := by
        rw [hsplit, List.length_append]; simp [List.length_cons]; omega
      have hmid_lt_full : pre.length < decls.pairs.toList.length := by
        rw [hsplit, List.length_append]
        exact Nat.lt_add_of_pos_right (Nat.zero_lt_succ _)
      have hlist_ipost : decls.pairs.toList[pre.length + (i + 1)]'hipost_lt_full =
          (g, Typed.Declaration.dataType td_dt) := by
        rw [show decls.pairs.toList[pre.length + (i + 1)]'hipost_lt_full =
            (pre ++ (g, Typed.Declaration.dataType td_dt) :: post)[pre.length + (i + 1)]'(by
              rw [List.length_append]; simp [List.length_cons]; omega) from by
          congr 1 <;> exact hsplit]
        rw [List.getElem_append_right (by omega : pre.length ≤ pre.length + (i + 1))]
        simp
        exact hi_eq
      have hlist_mid : decls.pairs.toList[pre.length]'hmid_lt_full =
          (g, Typed.Declaration.dataType td_dt) := by
        rw [show decls.pairs.toList[pre.length]'hmid_lt_full =
            (pre ++ (g, Typed.Declaration.dataType td_dt) :: post)[pre.length]'(by
              rw [List.length_append]
              exact Nat.lt_add_of_pos_right (Nat.zero_lt_succ _)) from by
          congr 1 <;> exact hsplit]
        rw [List.getElem_append_right (Nat.le_refl _)]
        simp
      have hkey_eq : ((decls.pairs.toList[pre.length + (i + 1)]'hipost_lt_full).1 ==
          (decls.pairs.toList[pre.length]'hmid_lt_full).1) = true := by
        rw [hlist_ipost, hlist_mid]; simp
      have hij := indexMap_pairs_index_unique_of_key decls hipost_lt_full hmid_lt_full hkey_eq
      omega
  rw [hsplit]
  rw [List.foldl_append]
  rw [List.foldl_cons]
  obtain ⟨md_dt, hstep⟩ := srcStep_at_g_inserts_dataType decls mono
    (List.foldl (srcStep decls mono) default pre) hdt_params (g := g) (td_dt := td_dt)
  rw [srcStep_foldl_no_g_preserves decls mono post _ hno_g_post]
  exact ⟨md_dt, hstep⟩

/-- Inner ctor-fold preserves dataType-kind at `g` when no inner ctor key
equals `g`. -/
private theorem dtCtorFold_preserves_dataType_kind
    (mono : MonoMap) (dt : DataType) (newDt : DataType)
    {g : Global} :
    ∀ (cs : List Constructor) (acc : Typed.Decls)
      (_hCtorNotKey : ∀ c ∈ cs, dt.name.pushNamespace c.nameHead ≠ g)
      (_hacc : ∃ md_dt, acc.getByKey g = some (.dataType md_dt)),
    ∃ md_dt,
      (cs.foldl
        (fun acc'' c =>
          let cName := dt.name.pushNamespace c.nameHead
          acc''.insert cName (.constructor newDt c))
        acc).getByKey g = some (.dataType md_dt)
  | [], _, _, hacc => hacc
  | c :: rest, acc, hCtorNotKey, hacc => by
    simp only [List.foldl_cons]
    have hne : (dt.name.pushNamespace c.nameHead == g) = false := by
      rw [beq_eq_false_iff_ne]; exact hCtorNotKey c List.mem_cons_self
    have hacc' : ∃ md_dt,
        (acc.insert (dt.name.pushNamespace c.nameHead)
          (.constructor newDt c)).getByKey g = some (.dataType md_dt) := by
      obtain ⟨md_dt, hget⟩ := hacc
      refine ⟨md_dt, ?_⟩
      rw [IndexMap.getByKey_insert_of_beq_false _ _ hne]
      exact hget
    exact dtCtorFold_preserves_dataType_kind mono dt newDt rest _
      (fun c' hc' => hCtorNotKey c' (List.mem_cons_of_mem _ hc')) hacc'

/-- A single step of `dtStep` preserves dataType-kind at `g` when no inner
ctor key equals `g`. The `dt.name = g` case re-inserts `.dataType`. -/
private theorem dtStep_preserves_dataType_kind
    (mono : MonoMap) (acc : Typed.Decls) (dt : DataType)
    {g : Global}
    (hCtorNotKey : ∀ c ∈ dt.constructors, dt.name.pushNamespace c.nameHead ≠ g)
    (hacc : ∃ md_dt, acc.getByKey g = some (.dataType md_dt)) :
    ∃ md_dt, (dtStep mono acc dt).getByKey g = some (.dataType md_dt) := by
  unfold dtStep
  let emptySubst : Global → Option Typ := fun _ => none
  let rewrittenCtors := dt.constructors.map fun c =>
    { c with argTypes := c.argTypes.map (rewriteTyp emptySubst mono) }
  let newDt : DataType := { dt with constructors := rewrittenCtors }
  -- After the dt.name insert, kind at g is `.dataType` (either we re-insert
  -- newDt at g, or the insert is at a different key and acc's value is preserved).
  have hacc_after_dtinsert : ∃ md_dt,
      (acc.insert dt.name (Typed.Declaration.dataType newDt)).getByKey g =
        some (.dataType md_dt) := by
    by_cases hbeq : (dt.name == g) = true
    · refine ⟨newDt, ?_⟩
      have heq : dt.name = g := LawfulBEq.eq_of_beq hbeq
      rw [heq]
      exact IndexMap.getByKey_insert_self _ _ _
    · have hne : (dt.name == g) = false := Bool.not_eq_true _ |>.mp hbeq
      obtain ⟨md_dt, hget⟩ := hacc
      refine ⟨md_dt, ?_⟩
      rw [IndexMap.getByKey_insert_of_beq_false _ _ hne]
      exact hget
  -- Inner ctor fold: rewrittenCtors share nameHeads with dt.constructors.
  have hCtorNotKey' : ∀ c ∈ rewrittenCtors,
      dt.name.pushNamespace c.nameHead ≠ g := by
    intro c hc
    -- c ∈ rewrittenCtors = dt.constructors.map (fun c' => { c' with argTypes := ... }).
    have hmap : c ∈ dt.constructors.map (fun c' =>
        { c' with argTypes := c'.argTypes.map (rewriteTyp emptySubst mono) }) := hc
    obtain ⟨c_orig, hc_orig_mem, hc_orig_eq⟩ := List.mem_map.mp hmap
    have hnh : c.nameHead = c_orig.nameHead := by rw [← hc_orig_eq]
    rw [hnh]
    exact hCtorNotKey c_orig hc_orig_mem
  exact dtCtorFold_preserves_dataType_kind mono dt newDt rewrittenCtors _ hCtorNotKey' hacc_after_dtinsert

/-- `dtStep` Array foldl preserves dataType-kind at `g` under
`hDtCtorNotKey`. -/
private theorem dtStep_foldl_preserves_dataType_kind
    (mono : MonoMap) (newDataTypes : Array DataType) (init : Typed.Decls)
    {g : Global}
    (hinit : ∃ md_dt, init.getByKey g = some (.dataType md_dt))
    (hDtCtorNotKey : ∀ dt ∈ newDataTypes, ∀ c ∈ dt.constructors,
      dt.name.pushNamespace c.nameHead ≠ g) :
    ∃ md_dt,
      (newDataTypes.foldl (dtStep mono) init).getByKey g =
        some (.dataType md_dt) := by
  apply Array.foldl_induction
    (motive := fun (_ : Nat) (acc : Typed.Decls) =>
      ∃ md_dt, acc.getByKey g = some (.dataType md_dt)) hinit
  intro i acc hinv
  have hCtorNotKey : ∀ c ∈ (newDataTypes[i.val]'i.isLt).constructors,
      (newDataTypes[i.val]'i.isLt).name.pushNamespace c.nameHead ≠ g :=
    hDtCtorNotKey _ (Array.getElem_mem _)
  exact dtStep_preserves_dataType_kind mono acc _ hCtorNotKey hinv

/-- A single step of `fnStep` on `f` with `f.name ≠ g` preserves
dataType-kind at `g`. -/
private theorem fnStep_preserves_dataType_kind
    (decls : Typed.Decls) (mono : MonoMap) (acc : Typed.Decls) (f : Typed.Function)
    {g : Global}
    (hfn_ne : f.name ≠ g)
    (hacc : ∃ md_dt, acc.getByKey g = some (.dataType md_dt)) :
    ∃ md_dt, (fnStep decls mono acc f).getByKey g = some (.dataType md_dt) := by
  unfold fnStep
  have hbeq : (f.name == g) = false := by
    rw [beq_eq_false_iff_ne]; exact hfn_ne
  obtain ⟨md_dt, hget⟩ := hacc
  refine ⟨md_dt, ?_⟩
  rw [IndexMap.getByKey_insert_of_beq_false _ _ hbeq]
  exact hget

/-- `fnStep` Array foldl preserves dataType-kind at `g` under `hFnNotKey`. -/
private theorem fnStep_foldl_preserves_dataType_kind
    (decls : Typed.Decls) (mono : MonoMap) (newFunctions : Array Typed.Function)
    (init : Typed.Decls) {g : Global}
    (hinit : ∃ md_dt, init.getByKey g = some (.dataType md_dt))
    (hFnNotKey : ∀ f ∈ newFunctions, f.name ≠ g) :
    ∃ md_dt,
      (newFunctions.foldl (fnStep decls mono) init).getByKey g =
        some (.dataType md_dt) := by
  apply Array.foldl_induction
    (motive := fun (_ : Nat) (acc : Typed.Decls) =>
      ∃ md_dt, acc.getByKey g = some (.dataType md_dt)) hinit
  intro i acc hinv
  have hfn_ne : (newFunctions[i.val]'i.isLt).name ≠ g :=
    hFnNotKey _ (Array.getElem_mem _)
  exact fnStep_preserves_dataType_kind decls mono acc _ hfn_ne hinv

/-- Phase A.2 main: `concretizeBuild` preserves dataType-kind from
typed→monoDecls. -/
theorem concretizeBuild_preserves_dataType_kind_fwd
    (decls : Typed.Decls) (mono : MonoMap)
    (newFunctions : Array Typed.Function) (newDataTypes : Array DataType)
    {g : Global} {td_dt : DataType}
    (hget : decls.getByKey g = some (.dataType td_dt))
    (hdt_params : td_dt.params = [])
    (hDtCtorNotKey : ∀ dt ∈ newDataTypes, ∀ c ∈ dt.constructors,
      dt.name.pushNamespace c.nameHead ≠ g)
    (hFnNotKey : ∀ f ∈ newFunctions, f.name ≠ g) :
    ∃ md_dt,
      (concretizeBuild decls mono newFunctions newDataTypes).getByKey g =
        some (.dataType md_dt) := by
  rw [concretizeBuild_eq]
  have h1 := fromSource_inserts_dataType_at_key decls mono hget hdt_params
  have h2 := dtStep_foldl_preserves_dataType_kind mono newDataTypes _ h1 hDtCtorNotKey
  exact fnStep_foldl_preserves_dataType_kind decls mono newFunctions _ h2 hFnNotKey

/-! #### Phase 0 — `concretizeBuild` lifts every newDt/newFn name to a
mono-decl entry. Used by `concretize_produces_mono_correspondence` to discharge
`dt_lifts` / `fn_lifts` / `has_new_decl`'s cd-existence prerequisite. -/

/-- A single step of `dtStep` on `dt` always inserts `.dataType` at `dt.name`
(the inner ctor fold inserts at `dt.name.pushNamespace c.nameHead ≠ dt.name`,
so the `.dataType` at `dt.name` is never disturbed). -/
private theorem dtStep_inserts_dataType_at_self
    (mono : MonoMap) (acc : Typed.Decls) (dt : DataType) :
    ∃ md_dt, (dtStep mono acc dt).getByKey dt.name = some (.dataType md_dt) := by
  unfold dtStep
  let emptySubst : Global → Option Typ := fun _ => none
  let rewrittenCtors := dt.constructors.map fun c =>
    { c with argTypes := c.argTypes.map (rewriteTyp emptySubst mono) }
  let newDt : DataType := { dt with constructors := rewrittenCtors }
  -- After the dt.name insert, kind at dt.name is `.dataType newDt`.
  -- The inner ctor fold inserts only at keys `dt.name.pushNamespace c.nameHead`,
  -- which differ from `dt.name` (Global.ne_pushNamespace).
  have hpreserve :
      ∀ (cs : List Constructor) (acc' : Typed.Decls)
        (_h : ∃ md, acc'.getByKey dt.name = some (.dataType md)),
        ∃ md, IndexMap.getByKey
          (cs.foldl (fun acc'' c =>
            acc''.insert (dt.name.pushNamespace c.nameHead)
              (.constructor newDt c)) acc') dt.name = some (.dataType md) := by
    intro cs
    induction cs with
    | nil => intro acc' h; exact h
    | cons c rest ih =>
      intro acc' h
      simp only [List.foldl_cons]
      apply ih
      have hne : dt.name ≠ dt.name.pushNamespace c.nameHead :=
        Global.ne_pushNamespace dt.name c.nameHead
      have hbeq : (dt.name.pushNamespace c.nameHead == dt.name) = false := by
        rw [beq_eq_false_iff_ne]; exact (Ne.symm hne)
      obtain ⟨md, hmd⟩ := h
      refine ⟨md, ?_⟩
      rw [IndexMap.getByKey_insert_of_beq_false _ _ hbeq]
      exact hmd
  apply hpreserve
  refine ⟨newDt, ?_⟩
  exact IndexMap.getByKey_insert_self _ _ _

/-- `dtStep` foldl over a list, when `dt` ∈ list and no other step's ctor-key
collides with `dt.name`, ends with `.dataType` at `dt.name`. -/
private theorem dtStep_foldl_list_inserts_at_dt_name
    (mono : MonoMap) {dt : DataType} :
    ∀ (xs : List DataType) (init : Typed.Decls)
      (_hmem : dt ∈ xs)
      (_hCtorNotKey : ∀ dt' ∈ xs, ∀ c ∈ dt'.constructors,
        dt'.name.pushNamespace c.nameHead ≠ dt.name),
    ∃ md_dt, (xs.foldl (dtStep mono) init).getByKey dt.name =
      some (.dataType md_dt)
  | [], _, hmem, _ => by cases hmem
  | hd :: rest, init, hmem, hCtorNotKey => by
    simp only [List.foldl_cons]
    rw [List.mem_cons] at hmem
    rcases hmem with hmem_hd | hmem_rest
    · -- dt = hd. Apply dtStep_inserts_dataType_at_self at hd, then preserve over rest.
      subst hmem_hd
      have h1 := dtStep_inserts_dataType_at_self mono init dt
      -- Continue over rest; need rest's ctor-keys don't equal dt.name.
      have hrest_ctor : ∀ dt' ∈ rest, ∀ c ∈ dt'.constructors,
          dt'.name.pushNamespace c.nameHead ≠ dt.name := by
        intro dt' hdt' c hc
        exact hCtorNotKey dt' (List.mem_cons_of_mem _ hdt') c hc
      clear hCtorNotKey
      -- Convert `rest.foldl ...` to Array form to leverage `dtStep_foldl_preserves_dataType_kind`.
      have heq : rest.foldl (dtStep mono) (dtStep mono init dt)
          = rest.toArray.foldl (dtStep mono) (dtStep mono init dt) := by
        rw [Array.foldl_toList]
      rw [heq]
      apply dtStep_foldl_preserves_dataType_kind mono rest.toArray _ h1
      intro dt' hdt' c hc
      have hdt'_list : dt' ∈ rest := by
        have := Array.mem_toList_iff.mpr hdt'
        simpa using this
      exact hrest_ctor dt' hdt'_list c hc
    · -- dt ∈ rest. Use IH on rest; prepend dtStep mono init hd.
      have hrest_ctor : ∀ dt' ∈ rest, ∀ c ∈ dt'.constructors,
          dt'.name.pushNamespace c.nameHead ≠ dt.name := by
        intro dt' hdt' c hc
        exact hCtorNotKey dt' (List.mem_cons_of_mem _ hdt') c hc
      exact dtStep_foldl_list_inserts_at_dt_name mono rest
        (dtStep mono init hd) hmem_rest hrest_ctor

/-- `dtStep` Array foldl inserts `.dataType` at `dt.name` for every `dt ∈
newDataTypes`, under the disjointness `hDtCtorNotKey`. -/
private theorem dtStep_foldl_inserts_at_dt_name
    (mono : MonoMap) (newDataTypes : Array DataType)
    (init : Typed.Decls) {dt : DataType} (hmem : dt ∈ newDataTypes)
    (hDtCtorNotKey : ∀ dt' ∈ newDataTypes, ∀ c ∈ dt'.constructors,
      dt'.name.pushNamespace c.nameHead ≠ dt.name) :
    ∃ md_dt,
      (newDataTypes.foldl (dtStep mono) init).getByKey dt.name =
        some (.dataType md_dt) := by
  rw [← Array.foldl_toList]
  have hmem' : dt ∈ newDataTypes.toList := Array.mem_toList_iff.mpr hmem
  have hCtor' : ∀ dt' ∈ newDataTypes.toList, ∀ c ∈ dt'.constructors,
      dt'.name.pushNamespace c.nameHead ≠ dt.name := by
    intro dt' hdt'; exact hDtCtorNotKey dt' (Array.mem_toList_iff.mp hdt')
  exact dtStep_foldl_list_inserts_at_dt_name mono newDataTypes.toList init hmem' hCtor'

/-- A single `fnStep` step preserves `.function`-kind at any key `g` (regardless
of `f.name = g` or not). When `f.name = g`, the insert overrides to a fresh
`.function`; when `f.name ≠ g`, the insert preserves the prior value. -/
private theorem fnStep_preserves_function_kind
    (decls : Typed.Decls) (mono : MonoMap) (acc : Typed.Decls) (f : Typed.Function)
    {g : Global}
    (hacc : ∃ md_f, acc.getByKey g = some (.function md_f)) :
    ∃ md_f, (fnStep decls mono acc f).getByKey g = some (.function md_f) := by
  unfold fnStep
  by_cases hbeq : (f.name == g) = true
  · let emptySubst : Global → Option Typ := fun _ => none
    let newF : Typed.Function :=
      { f with
        inputs := f.inputs.map fun (l, t) => (l, rewriteTyp emptySubst mono t),
        output := rewriteTyp emptySubst mono f.output,
        body := rewriteTypedTerm decls emptySubst mono f.body }
    refine ⟨newF, ?_⟩
    have heq : f.name = g := LawfulBEq.eq_of_beq hbeq
    rw [← heq]
    exact IndexMap.getByKey_insert_self _ _ _
  · have hbeq' : (f.name == g) = false := Bool.not_eq_true _ |>.mp hbeq
    obtain ⟨md_f, hget⟩ := hacc
    refine ⟨md_f, ?_⟩
    rw [IndexMap.getByKey_insert_of_beq_false _ _ hbeq']
    exact hget

/-- `fnStep` foldl preserves `.function`-kind at any key (no disjointness
needed: `fnStep` always inserts `.function`, so re-inserting at the same key
doesn't change the kind). -/
private theorem fnStep_foldl_preserves_function_kind
    (decls : Typed.Decls) (mono : MonoMap) (newFunctions : Array Typed.Function)
    (init : Typed.Decls) {g : Global}
    (hinit : ∃ md_f, init.getByKey g = some (.function md_f)) :
    ∃ md_f, (newFunctions.foldl (fnStep decls mono) init).getByKey g =
      some (.function md_f) := by
  apply Array.foldl_induction
    (motive := fun (_ : Nat) (acc : Typed.Decls) =>
      ∃ md_f, acc.getByKey g = some (.function md_f)) hinit
  intro i acc hinv
  exact fnStep_preserves_function_kind decls mono acc _ hinv

/-- `fnStep` foldl inserts `.function` at `f.name` for every `f ∈
newFunctions`. The list-form does case-analysis on whether the head equals f
or recurses on the tail. -/
private theorem fnStep_foldl_list_inserts_at_fn_name
    (decls : Typed.Decls) (mono : MonoMap) {f : Typed.Function} :
    ∀ (xs : List Typed.Function) (init : Typed.Decls)
      (_hmem : f ∈ xs),
    ∃ md_f, (xs.foldl (fnStep decls mono) init).getByKey f.name =
      some (.function md_f)
  | [], _, hmem => by cases hmem
  | hd :: rest, init, hmem => by
    simp only [List.foldl_cons]
    rw [List.mem_cons] at hmem
    rcases hmem with hmem_hd | hmem_rest
    · -- f = hd. fnStep on f inserts `.function` at f.name. Then preserve over rest.
      subst hmem_hd
      let emptySubst : Global → Option Typ := fun _ => none
      let newF : Typed.Function :=
        { f with
          inputs := f.inputs.map fun (l, t) => (l, rewriteTyp emptySubst mono t),
          output := rewriteTyp emptySubst mono f.output,
          body := rewriteTypedTerm decls emptySubst mono f.body }
      have hstep : ∃ md_f, (fnStep decls mono init f).getByKey f.name =
          some (.function md_f) := by
        refine ⟨newF, ?_⟩
        unfold fnStep
        exact IndexMap.getByKey_insert_self _ _ _
      -- Convert rest's foldl to Array form via fnStep_foldl_preserves_function_kind.
      have heq' : rest.foldl (fnStep decls mono) (fnStep decls mono init f)
          = rest.toArray.foldl (fnStep decls mono) (fnStep decls mono init f) := by
        rw [Array.foldl_toList]
      rw [heq']
      exact fnStep_foldl_preserves_function_kind decls mono rest.toArray
        (fnStep decls mono init f) hstep
    · -- f ∈ rest. Recurse.
      exact fnStep_foldl_list_inserts_at_fn_name decls mono rest
        (fnStep decls mono init hd) hmem_rest

/-- `fnStep` Array foldl inserts `.function` at `f.name` for every `f ∈
newFunctions`. -/
private theorem fnStep_foldl_inserts_at_fn_name
    (decls : Typed.Decls) (mono : MonoMap) (newFunctions : Array Typed.Function)
    (init : Typed.Decls) {f : Typed.Function} (hmem : f ∈ newFunctions) :
    ∃ md_f,
      (newFunctions.foldl (fnStep decls mono) init).getByKey f.name =
        some (.function md_f) := by
  rw [← Array.foldl_toList]
  exact fnStep_foldl_list_inserts_at_fn_name decls mono newFunctions.toList init
    (Array.mem_toList_iff.mpr hmem)

/-- Inner ctor-fold (used inside `dtStep`) preserves containsKey. -/
private theorem dtCtorFold_preserves_containsKey
    (newDt : DataType) (cName : String → Global) (newD : Constructor → Typed.Declaration)
    {g : Global} :
    ∀ (cs : List Constructor) (acc : Typed.Decls),
      acc.containsKey g →
      (cs.foldl (fun acc'' c => acc''.insert (cName c.nameHead) (newD c)) acc).containsKey g
  | [], _, h => h
  | c :: rest, acc, h => by
    simp only [List.foldl_cons]
    exact dtCtorFold_preserves_containsKey newDt cName newD rest _
      (IndexMap.containsKey_insert_preserves _ _ _ _ h)

/-- `dtStep` is insert-only: containsKey is preserved across single steps. -/
private theorem dtStep_preserves_containsKey
    (mono : MonoMap) (acc : Typed.Decls) (dt : DataType) {g : Global}
    (hacc : acc.containsKey g) :
    (dtStep mono acc dt).containsKey g := by
  unfold dtStep
  let emptySubst : Global → Option Typ := fun _ => none
  let rewrittenCtors := dt.constructors.map fun c =>
    { c with argTypes := c.argTypes.map (rewriteTyp emptySubst mono) }
  let newDt : DataType := { dt with constructors := rewrittenCtors }
  -- After acc.insert dt.name, containsKey preserved; then the ctor fold preserves.
  have hafter : (acc.insert dt.name (.dataType newDt)).containsKey g :=
    IndexMap.containsKey_insert_preserves _ _ _ _ hacc
  exact dtCtorFold_preserves_containsKey newDt
    (fun s => dt.name.pushNamespace s) (fun c => .constructor newDt c)
    rewrittenCtors _ hafter

/-- `dtStep` foldl preserves containsKey. -/
private theorem dtStep_foldl_preserves_containsKey
    (mono : MonoMap) (newDataTypes : Array DataType)
    (init : Typed.Decls) {g : Global}
    (hinit : init.containsKey g) :
    (newDataTypes.foldl (dtStep mono) init).containsKey g := by
  apply Array.foldl_induction
    (motive := fun (_ : Nat) (acc : Typed.Decls) => acc.containsKey g) hinit
  intro i acc hinv
  exact dtStep_preserves_containsKey mono acc _ hinv

/-- `dtStep mono acc dt` always sets `containsKey dt.name`. -/
private theorem dtStep_inserts_containsKey_self
    (mono : MonoMap) (acc : Typed.Decls) (dt : DataType) :
    (dtStep mono acc dt).containsKey dt.name := by
  obtain ⟨md_dt, hget⟩ := dtStep_inserts_dataType_at_self mono acc dt
  exact (IndexMap.getByKey_isSome_iff_containsKey _ _).mp (by rw [hget]; rfl)

/-- `fnStep` is insert-only: containsKey is preserved. -/
private theorem fnStep_preserves_containsKey
    (decls : Typed.Decls) (mono : MonoMap) (acc : Typed.Decls) (f : Typed.Function)
    {g : Global} (hacc : acc.containsKey g) :
    (fnStep decls mono acc f).containsKey g := by
  unfold fnStep
  exact IndexMap.containsKey_insert_preserves _ _ _ _ hacc

/-- `fnStep` foldl preserves containsKey. -/
private theorem fnStep_foldl_preserves_containsKey
    (decls : Typed.Decls) (mono : MonoMap) (newFunctions : Array Typed.Function)
    (init : Typed.Decls) {g : Global}
    (hinit : init.containsKey g) :
    (newFunctions.foldl (fnStep decls mono) init).containsKey g := by
  apply Array.foldl_induction
    (motive := fun (_ : Nat) (acc : Typed.Decls) => acc.containsKey g) hinit
  intro i acc hinv
  exact fnStep_preserves_containsKey decls mono acc _ hinv

/-- For every `dt ∈ newDataTypes`, `concretizeBuild`'s output contains `dt.name`
as a key (kind not specified — could be `.dataType` or `.constructor` if a
later inner-ctor key collides). Used to discharge cd-existence in
`concretize_produces_mono_correspondence`'s `has_new_decl` and `dt_lifts`. -/
private theorem concretizeBuild_containsKey_newDt_name
    (typedDecls : Typed.Decls) (mono : MonoMap)
    (newFunctions : Array Typed.Function) (newDataTypes : Array DataType)
    {dt : DataType} (hmem : dt ∈ newDataTypes) :
    (concretizeBuild typedDecls mono newFunctions newDataTypes).containsKey dt.name := by
  rw [concretizeBuild_eq]
  apply fnStep_foldl_preserves_containsKey
  -- Reduce dtStep foldl to a list-form split at dt's position, then preserve.
  rw [← Array.foldl_toList]
  have hmem' : dt ∈ newDataTypes.toList := Array.mem_toList_iff.mpr hmem
  obtain ⟨pre, post, hsplit⟩ := List.append_of_mem hmem'
  rw [hsplit, List.foldl_append, List.foldl_cons]
  -- After the dtStep on dt, containsKey dt.name is set. Then foldl over post preserves.
  have h1 : (dtStep mono (List.foldl (dtStep mono) (typedDecls.pairs.foldl
      (srcStep typedDecls mono) default) pre) dt).containsKey dt.name :=
    dtStep_inserts_containsKey_self mono _ dt
  -- Convert post.foldl to Array form.
  have hconv : List.foldl (dtStep mono) (dtStep mono (List.foldl (dtStep mono)
      (typedDecls.pairs.foldl (srcStep typedDecls mono) default) pre) dt) post
      = post.toArray.foldl (dtStep mono) (dtStep mono (List.foldl (dtStep mono)
        (typedDecls.pairs.foldl (srcStep typedDecls mono) default) pre) dt) := by
    rw [Array.foldl_toList]
  rw [hconv]
  exact dtStep_foldl_preserves_containsKey mono post.toArray _ h1

/-- Inner ctor-fold inserts `.constructor newDt c'` at
`dt.name.pushNamespace nh` whenever some `c' ∈ cs` has `c'.nameHead = nh`.
After the matching insertion, `dtCtorFold_preserves_ctor_kind` handles
preservation across the rest of the fold (each subsequent ctor insert is
also a `.constructor`, so the kind is preserved unconditionally). -/
private theorem dtCtorFold_inserts_at_nameHead
    (mono : MonoMap) (dt : DataType) (newDt : DataType) (nh : String) :
    ∀ (cs : List Constructor) (acc : Typed.Decls)
      (_hmem : ∃ c' ∈ cs, c'.nameHead = nh),
    ∃ md_dt md_c,
      (cs.foldl
        (fun acc'' c =>
          let cName := dt.name.pushNamespace c.nameHead
          acc''.insert cName (.constructor newDt c))
        acc).getByKey (dt.name.pushNamespace nh) = some (.constructor md_dt md_c)
  | [], _, hmem => by
      obtain ⟨_, hc_mem, _⟩ := hmem
      cases hc_mem
  | c :: rest, acc, hmem => by
    simp only [List.foldl_cons]
    by_cases hnh : c.nameHead = nh
    · -- This step inserts at `dt.name.pushNamespace nh`. After it, the value
      -- there is `.constructor newDt c`. Continue with preservation over rest.
      have h1 : ∃ md_dt md_c,
          (acc.insert (dt.name.pushNamespace c.nameHead)
            (.constructor newDt c)).getByKey (dt.name.pushNamespace nh) =
            some (.constructor md_dt md_c) := by
        refine ⟨newDt, c, ?_⟩
        rw [hnh]
        exact IndexMap.getByKey_insert_self _ _ _
      exact dtCtorFold_preserves_ctor_kind mono dt newDt rest _ h1
    · -- This step doesn't hit `nh`. Recurse: nh must come from some c' ∈ rest.
      obtain ⟨c', hc'_mem, hc'_nh⟩ := hmem
      rw [List.mem_cons] at hc'_mem
      rcases hc'_mem with rfl | hc'_rest
      · exact absurd hc'_nh hnh
      · exact dtCtorFold_inserts_at_nameHead mono dt newDt nh rest _
          ⟨c', hc'_rest, hc'_nh⟩

/-- A single step of `dtStep` on `dt` with `c ∈ dt.constructors` always sets
ctor-kind at `dt.name.pushNamespace c.nameHead` (the inner ctor fold inserts
the rewritten counterpart of `c` at this key). -/
private theorem dtStep_inserts_ctor_at_self_ctor
    (mono : MonoMap) (acc : Typed.Decls) (dt : DataType)
    {c : Constructor} (hc : c ∈ dt.constructors) :
    ∃ md_dt md_c,
      (dtStep mono acc dt).getByKey (dt.name.pushNamespace c.nameHead) =
        some (.constructor md_dt md_c) := by
  unfold dtStep
  let emptySubst : Global → Option Typ := fun _ => none
  let rewrittenCtors := dt.constructors.map fun c' =>
    { c' with argTypes := c'.argTypes.map (rewriteTyp emptySubst mono) }
  let newDt : DataType := { dt with constructors := rewrittenCtors }
  -- Find rewritten counterpart of c, with same nameHead.
  have hrewmem : ∃ c'' ∈ rewrittenCtors, c''.nameHead = c.nameHead := by
    refine ⟨{ c with argTypes := c.argTypes.map (rewriteTyp emptySubst mono) }, ?_, rfl⟩
    exact List.mem_map_of_mem hc
  exact dtCtorFold_inserts_at_nameHead mono dt newDt c.nameHead rewrittenCtors _ hrewmem

/-- A single step of `dtStep` on `dt'` (possibly different from the target dt)
preserves ctor-kind at `g`, provided `dt'.name ≠ g`. The inner ctor fold
either re-inserts a `.constructor` at `g` (preserving ctor-kind) or doesn't
hit `g` (preserving the existing ctor entry). -/
private theorem dtStep_preserves_ctor_kind_at_unconditional
    (mono : MonoMap) (acc : Typed.Decls) (dt' : DataType)
    {g : Global}
    (hdt'_ne : dt'.name ≠ g)
    (hacc : ∃ md_dt md_c, acc.getByKey g = some (.constructor md_dt md_c)) :
    ∃ md_dt md_c, (dtStep mono acc dt').getByKey g = some (.constructor md_dt md_c) :=
  dtStep_preserves_ctor_kind mono acc dt' hdt'_ne hacc

/-- `dtStep` Array foldl preserves ctor-kind at `g` under `hDtNotKey`. The
inner ctor fold's potential re-insertion at `g` is benign — it inserts a
`.constructor`, preserving ctor-kind. -/
private theorem dtStep_foldl_preserves_ctor_kind_at
    (mono : MonoMap) (newDataTypes : Array DataType) (init : Typed.Decls)
    {g : Global}
    (hinit : ∃ md_dt md_c, init.getByKey g = some (.constructor md_dt md_c))
    (hDtNotKey : ∀ dt' ∈ newDataTypes, dt'.name ≠ g) :
    ∃ md_dt md_c,
      (newDataTypes.foldl (dtStep mono) init).getByKey g =
        some (.constructor md_dt md_c) :=
  dtStep_foldl_preserves_ctor_kind mono newDataTypes init hinit hDtNotKey

/-- `dtStep` foldl over a list inserts ctor-kind at `dt.name.pushNamespace
c.nameHead` for `dt ∈ xs` and `c ∈ dt.constructors`, under `hDtNotKey`. -/
private theorem dtStep_foldl_list_inserts_at_dt_ctor_name
    (mono : MonoMap) {dt : DataType} {c : Constructor} (hc : c ∈ dt.constructors) :
    ∀ (xs : List DataType) (init : Typed.Decls)
      (_hmem : dt ∈ xs)
      (_hDtNotKey : ∀ dt' ∈ xs, dt'.name ≠ dt.name.pushNamespace c.nameHead),
    ∃ md_dt md_c,
      (xs.foldl (dtStep mono) init).getByKey (dt.name.pushNamespace c.nameHead) =
        some (.constructor md_dt md_c)
  | [], _, hmem, _ => by cases hmem
  | hd :: rest, init, hmem, hDtNotKey => by
    simp only [List.foldl_cons]
    rw [List.mem_cons] at hmem
    rcases hmem with hmem_hd | hmem_rest
    · subst hmem_hd
      have h1 := dtStep_inserts_ctor_at_self_ctor mono init dt hc
      have hrest_dt : ∀ dt' ∈ rest, dt'.name ≠ dt.name.pushNamespace c.nameHead := by
        intro dt' hdt'
        exact hDtNotKey dt' (List.mem_cons_of_mem _ hdt')
      have heq : rest.foldl (dtStep mono) (dtStep mono init dt)
          = rest.toArray.foldl (dtStep mono) (dtStep mono init dt) := by
        rw [Array.foldl_toList]
      rw [heq]
      apply dtStep_foldl_preserves_ctor_kind_at mono rest.toArray _ h1
      intro dt' hdt'
      have hdt'_list : dt' ∈ rest := by
        have := Array.mem_toList_iff.mpr hdt'
        simpa using this
      exact hrest_dt dt' hdt'_list
    · have hrest_dt : ∀ dt' ∈ rest, dt'.name ≠ dt.name.pushNamespace c.nameHead := by
        intro dt' hdt'
        exact hDtNotKey dt' (List.mem_cons_of_mem _ hdt')
      exact dtStep_foldl_list_inserts_at_dt_ctor_name mono hc rest
        (dtStep mono init hd) hmem_rest hrest_dt

/-- `dtStep` Array foldl inserts ctor-kind at `dt.name.pushNamespace c.nameHead`
for every `dt ∈ newDataTypes` and `c ∈ dt.constructors`, under
`hDtNotKey`. -/
private theorem dtStep_foldl_inserts_at_dt_ctor_name
    (mono : MonoMap) (newDataTypes : Array DataType)
    (init : Typed.Decls) {dt : DataType} (hmem : dt ∈ newDataTypes)
    {c : Constructor} (hc : c ∈ dt.constructors)
    (hDtNotKey : ∀ dt' ∈ newDataTypes, dt'.name ≠ dt.name.pushNamespace c.nameHead) :
    ∃ md_dt md_c,
      (newDataTypes.foldl (dtStep mono) init).getByKey
        (dt.name.pushNamespace c.nameHead) = some (.constructor md_dt md_c) := by
  rw [← Array.foldl_toList]
  have hmem' : dt ∈ newDataTypes.toList := Array.mem_toList_iff.mpr hmem
  have hDt' : ∀ dt' ∈ newDataTypes.toList, dt'.name ≠ dt.name.pushNamespace c.nameHead := by
    intro dt' hdt'
    exact hDtNotKey dt' (Array.mem_toList_iff.mp hdt')
  exact dtStep_foldl_list_inserts_at_dt_ctor_name mono hc newDataTypes.toList init
    hmem' hDt'

/-- Key lemma for `concretize_produces_mono_correspondence`'s `ctor_lifts` arm:
every `dt ∈ newDataTypes` and `c ∈ dt.constructors` has `.constructor _ _` at
`dt.name.pushNamespace c.nameHead` in `concretizeBuild`'s output, under
disjointness with newFunctions names and other newDataTypes names. -/
private theorem concretizeBuild_at_newDt_ctor_name
    (typedDecls : Typed.Decls) (mono : MonoMap)
    (newFunctions : Array Typed.Function) (newDataTypes : Array DataType)
    {dt : DataType} (hmem : dt ∈ newDataTypes)
    {c : Constructor} (hc : c ∈ dt.constructors)
    (hDtNotKey : ∀ dt' ∈ newDataTypes,
      dt'.name ≠ dt.name.pushNamespace c.nameHead)
    (hFnNotKey : ∀ f ∈ newFunctions,
      f.name ≠ dt.name.pushNamespace c.nameHead) :
    ∃ md_dt md_c,
      (concretizeBuild typedDecls mono newFunctions newDataTypes).getByKey
        (dt.name.pushNamespace c.nameHead) =
        some (.constructor md_dt md_c) := by
  rw [concretizeBuild_eq]
  have h2 := dtStep_foldl_inserts_at_dt_ctor_name mono newDataTypes
    (typedDecls.pairs.foldl (srcStep typedDecls mono) default) hmem hc hDtNotKey
  exact fnStep_foldl_preserves_ctor_kind typedDecls mono newFunctions _ h2 hFnNotKey

/-- Key lemma for `concretize_produces_mono_correspondence`'s `dt_lifts` arm:
every newly-pushed datatype's name is keyed to a `.dataType` in
`concretizeBuild`'s output, under disjointness with newFunctions names. -/
private theorem concretizeBuild_at_newDt_name
    (typedDecls : Typed.Decls) (mono : MonoMap)
    (newFunctions : Array Typed.Function) (newDataTypes : Array DataType)
    {dt : DataType} (hmem : dt ∈ newDataTypes)
    (hDtCtorNotKey : ∀ dt' ∈ newDataTypes, ∀ c ∈ dt'.constructors,
      dt'.name.pushNamespace c.nameHead ≠ dt.name)
    (hFnNotKey : ∀ f ∈ newFunctions, f.name ≠ dt.name) :
    ∃ md_dt,
      (concretizeBuild typedDecls mono newFunctions newDataTypes).getByKey dt.name =
        some (.dataType md_dt) := by
  rw [concretizeBuild_eq]
  have h2 := dtStep_foldl_inserts_at_dt_name mono newDataTypes
    (typedDecls.pairs.foldl (srcStep typedDecls mono) default) hmem hDtCtorNotKey
  exact fnStep_foldl_preserves_dataType_kind typedDecls mono newFunctions _ h2 hFnNotKey

/-- Key lemma for `concretize_produces_mono_correspondence`'s `fn_lifts` arm:
every newly-pushed function's name is keyed to a `.function` in
`concretizeBuild`'s output. The fnStep fold ALWAYS yields `.function` at any
`f.name` regardless of prior dtStep state (since fnStep insert overrides). -/
private theorem concretizeBuild_at_newFn_name
    (typedDecls : Typed.Decls) (mono : MonoMap)
    (newFunctions : Array Typed.Function) (newDataTypes : Array DataType)
    {f : Typed.Function} (hmem : f ∈ newFunctions) :
    ∃ md_f,
      (concretizeBuild typedDecls mono newFunctions newDataTypes).getByKey f.name =
        some (.function md_f) := by
  rw [concretizeBuild_eq]
  exact fnStep_foldl_inserts_at_fn_name typedDecls mono newFunctions _ hmem

/-! #### Explicit-structure version of `concretizeBuild_at_newDt_name`.

Mirrors `concretizeBuild_at_typed_ctor_explicit_general` but for the
`.dataType`-at-newDt-name case. Carries length + per-position nameHead
correspondence between the resulting `md_dt` and the source `dt` (the newDt
processed by `dtStep`). -/

/-- Structural payload: `d` is `.dataType md_dt` with constructors-list
length-equal and per-position `nameHead`-equal to `dt`'s constructors. -/
private def DtMatchesNH (dt : DataType) (d : Typed.Declaration) : Prop :=
  ∃ md_dt, d = .dataType md_dt ∧
    md_dt.constructors.length = dt.constructors.length ∧
    (∀ i (hi : i < dt.constructors.length)
        (hi' : i < md_dt.constructors.length),
      (md_dt.constructors[i]'hi').nameHead = (dt.constructors[i]'hi).nameHead)

/-- The literal `newDt = {dt with constructors := rewrittenCtors}` produced
by `dtStep mono _ dt` satisfies `DtMatchesNH dt`. -/
private theorem DtMatchesNH_self
    (mono : MonoMap) (dt : DataType) :
    let emptySubst : Global → Option Typ := fun _ => none
    let rewrittenCtors := dt.constructors.map fun c =>
      { c with argTypes := c.argTypes.map (rewriteTyp emptySubst mono) }
    let newDt : DataType := { dt with constructors := rewrittenCtors }
    DtMatchesNH dt (.dataType newDt) := by
  refine ⟨_, rfl, ?_, ?_⟩
  · simp only [List.length_map]
  · intro i hi _hi'
    simp only [List.getElem_map]

/-- Inner ctor-fold preserves `DtMatchesNH` at `g` when no inner ctor key
equals `g`. -/
private theorem dtCtorFold_preserves_DtMatchesNH
    (mono : MonoMap) (dt : DataType) (newDt : DataType) (target_dt : DataType)
    {g : Global} :
    ∀ (cs : List Constructor) (acc : Typed.Decls)
      (_hCtorNotKey : ∀ c ∈ cs, dt.name.pushNamespace c.nameHead ≠ g)
      (_hacc : ∃ d, acc.getByKey g = some d ∧ DtMatchesNH target_dt d),
    ∃ d,
      (cs.foldl
        (fun acc'' c =>
          let cName := dt.name.pushNamespace c.nameHead
          acc''.insert cName (.constructor newDt c))
        acc).getByKey g = some d ∧ DtMatchesNH target_dt d
  | [], _, _, hacc => hacc
  | c :: rest, acc, hCtorNotKey, hacc => by
    simp only [List.foldl_cons]
    have hne : (dt.name.pushNamespace c.nameHead == g) = false := by
      rw [beq_eq_false_iff_ne]; exact hCtorNotKey c List.mem_cons_self
    have hacc' : ∃ d,
        (acc.insert (dt.name.pushNamespace c.nameHead)
          (.constructor newDt c)).getByKey g = some d ∧ DtMatchesNH target_dt d := by
      obtain ⟨d, hget, hM⟩ := hacc
      refine ⟨d, ?_, hM⟩
      rw [IndexMap.getByKey_insert_of_beq_false _ _ hne]
      exact hget
    exact dtCtorFold_preserves_DtMatchesNH mono dt newDt target_dt rest _
      (fun c' hc' => hCtorNotKey c' (List.mem_cons_of_mem _ hc')) hacc'

/-- A single step of `dtStep` on `dt` (= target_dt) inserts `.dataType newDt`
at `dt.name` with the structural payload of `target_dt = dt`. -/
private theorem dtStep_inserts_DtMatchesNH_self
    (mono : MonoMap) (acc : Typed.Decls) (dt : DataType) :
    ∃ d, (dtStep mono acc dt).getByKey dt.name = some d ∧ DtMatchesNH dt d := by
  unfold dtStep
  let emptySubst : Global → Option Typ := fun _ => none
  let rewrittenCtors := dt.constructors.map fun c =>
    { c with argTypes := c.argTypes.map (rewriteTyp emptySubst mono) }
  let newDt : DataType := { dt with constructors := rewrittenCtors }
  -- After dt.name insert: value is `.dataType newDt` satisfying `DtMatchesNH dt`.
  have hacc_after : ∃ d,
      (acc.insert dt.name (Typed.Declaration.dataType newDt)).getByKey dt.name =
        some d ∧ DtMatchesNH dt d := by
    refine ⟨.dataType newDt, IndexMap.getByKey_insert_self _ _ _, ?_⟩
    exact DtMatchesNH_self mono dt
  -- Inner ctor fold preserves: each inner-key is `dt.name.pushNamespace c.nameHead`
  -- which differs from `dt.name` by `Global.ne_pushNamespace`.
  have hCtorNotKey : ∀ c ∈ rewrittenCtors,
      dt.name.pushNamespace c.nameHead ≠ dt.name :=
    fun c _ => (Global.ne_pushNamespace dt.name c.nameHead).symm
  exact dtCtorFold_preserves_DtMatchesNH mono dt newDt dt rewrittenCtors _
    hCtorNotKey hacc_after

/-- A single step of `dtStep` on `dt'` preserves `DtMatchesNH target_dt` at
`g` when `dt'.name ≠ g` (so the outer insert misses `g`) and no inner ctor
key of `dt'` equals `g`. -/
private theorem dtStep_preserves_DtMatchesNH
    (mono : MonoMap) (acc : Typed.Decls) (dt' : DataType) (target_dt : DataType)
    {g : Global}
    (hdt'_ne : dt'.name ≠ g)
    (hCtorNotKey : ∀ c ∈ dt'.constructors, dt'.name.pushNamespace c.nameHead ≠ g)
    (hacc : ∃ d, acc.getByKey g = some d ∧ DtMatchesNH target_dt d) :
    ∃ d, (dtStep mono acc dt').getByKey g = some d ∧ DtMatchesNH target_dt d := by
  unfold dtStep
  let emptySubst : Global → Option Typ := fun _ => none
  let rewrittenCtors := dt'.constructors.map fun c =>
    { c with argTypes := c.argTypes.map (rewriteTyp emptySubst mono) }
  let newDt' : DataType := { dt' with constructors := rewrittenCtors }
  -- After outer insert at dt'.name (≠ g), preserved.
  have hbeq_dt' : (dt'.name == g) = false := by
    rw [beq_eq_false_iff_ne]; exact hdt'_ne
  have hacc_after : ∃ d,
      (acc.insert dt'.name (Typed.Declaration.dataType newDt')).getByKey g =
        some d ∧ DtMatchesNH target_dt d := by
    obtain ⟨d, hget, hM⟩ := hacc
    refine ⟨d, ?_, hM⟩
    rw [IndexMap.getByKey_insert_of_beq_false _ _ hbeq_dt']
    exact hget
  -- Inner ctor fold preserves; rewrittenCtors share nameHeads with dt'.constructors.
  have hCtorNotKey' : ∀ c ∈ rewrittenCtors,
      dt'.name.pushNamespace c.nameHead ≠ g := by
    intro c hc
    have hmap : c ∈ dt'.constructors.map (fun c' =>
        { c' with argTypes := c'.argTypes.map (rewriteTyp emptySubst mono) }) := hc
    obtain ⟨c_orig, hc_orig_mem, hc_orig_eq⟩ := List.mem_map.mp hmap
    have hnh : c.nameHead = c_orig.nameHead := by rw [← hc_orig_eq]
    rw [hnh]
    exact hCtorNotKey c_orig hc_orig_mem
  exact dtCtorFold_preserves_DtMatchesNH mono dt' newDt' target_dt rewrittenCtors _
    hCtorNotKey' hacc_after

/-- `dtStep` foldl over a list inserts `.dataType` with `DtMatchesNH dt` at
`dt.name` for `dt ∈ xs`, under `hCtorNotKey` (no newDt's ctor inner-key equals
`dt.name`) and `hOtherDtNotKey` (no OTHER dt' ∈ xs has `dt'.name = dt.name`). -/
private theorem dtStep_foldl_list_inserts_DtMatchesNH_at_dt_name
    (mono : MonoMap) {dt : DataType} :
    ∀ (xs : List DataType) (init : Typed.Decls)
      (_hmem : dt ∈ xs)
      (_hCtorNotKey : ∀ dt' ∈ xs, ∀ c ∈ dt'.constructors,
        dt'.name.pushNamespace c.nameHead ≠ dt.name)
      (_hOtherDtNotKey : ∀ dt' ∈ xs, dt' ≠ dt → dt'.name ≠ dt.name),
    ∃ d, (xs.foldl (dtStep mono) init).getByKey dt.name = some d ∧
      DtMatchesNH dt d
  | [], _, hmem, _, _ => by cases hmem
  | hd :: rest, init, hmem, hCtorNotKey, hOtherDtNotKey => by
    simp only [List.foldl_cons]
    rw [List.mem_cons] at hmem
    rcases hmem with hmem_hd | hmem_rest
    · subst hmem_hd
      have h1 := dtStep_inserts_DtMatchesNH_self mono init dt
      have hrest_ctor : ∀ dt' ∈ rest, ∀ c ∈ dt'.constructors,
          dt'.name.pushNamespace c.nameHead ≠ dt.name := by
        intro dt' hdt' c hc
        exact hCtorNotKey dt' (List.mem_cons_of_mem _ hdt') c hc
      -- For each dt' ∈ rest with dt' ≠ dt, dt'.name ≠ dt.name.
      -- We strengthen: ALL dt' ∈ rest have dt'.name ≠ dt.name OR dt' = dt.
      -- The dt' = dt case is handled by structural equality: dtStep on the
      -- same dt produces the same newDt, so DtMatchesNH dt is preserved.
      -- Wait — but if dt' = dt, then dt'.name = dt.name, so the hypothesis
      -- hOtherDtNotKey doesn't fire (dt' ≠ dt is false → vacuous). To handle
      -- the dt' = dt case, observe: dtStep mono _ dt produces value with
      -- DtMatchesNH dt (by dtStep_inserts_DtMatchesNH_self). So a duplicate dt
      -- in rest would just re-overwrite with the same DtMatchesNH-correct value.
      have hrest_dt_struct : ∀ dt' ∈ rest, dt' = dt ∨ dt'.name ≠ dt.name := by
        intro dt' hdt'
        by_cases h : dt' = dt
        · left; exact h
        · right; exact hOtherDtNotKey dt' (List.mem_cons_of_mem _ hdt') h
      clear hCtorNotKey hOtherDtNotKey
      -- Generic preservation across rest.
      have hpreserve : ∀ (ys : List DataType) (acc : Typed.Decls),
          (∀ dt' ∈ ys, ∀ c ∈ dt'.constructors,
            dt'.name.pushNamespace c.nameHead ≠ dt.name) →
          (∀ dt' ∈ ys, dt' = dt ∨ dt'.name ≠ dt.name) →
          (∃ d, acc.getByKey dt.name = some d ∧ DtMatchesNH dt d) →
          ∃ d, (ys.foldl (dtStep mono) acc).getByKey dt.name = some d ∧
            DtMatchesNH dt d := by
        intro ys
        induction ys with
        | nil => intro acc _ _ h; exact h
        | cons dt' rest' ih =>
          intro acc hCtorAll hOrAll h
          simp only [List.foldl_cons]
          have hCtorNotKey_dt' : ∀ c ∈ dt'.constructors,
              dt'.name.pushNamespace c.nameHead ≠ dt.name :=
            hCtorAll dt' List.mem_cons_self
          have hOr_dt' : dt' = dt ∨ dt'.name ≠ dt.name :=
            hOrAll dt' List.mem_cons_self
          -- Step on dt': either dt' = dt (overwrites with self DtMatchesNH-good
          -- value) or dt'.name ≠ dt.name (outer insert misses dt.name).
          have hStep : ∃ d, (dtStep mono acc dt').getByKey dt.name = some d ∧
              DtMatchesNH dt d := by
            rcases hOr_dt' with hdteq | hne
            · -- dt' = dt: dtStep on dt overwrites with `.dataType newDt`
              -- satisfying DtMatchesNH dt.
              subst hdteq
              exact dtStep_inserts_DtMatchesNH_self mono acc dt'
            · exact dtStep_preserves_DtMatchesNH mono acc dt' dt hne
                hCtorNotKey_dt' h
          exact ih (dtStep mono acc dt')
            (fun dt'' hdt'' c hc => hCtorAll dt'' (List.mem_cons_of_mem _ hdt'') c hc)
            (fun dt'' hdt'' => hOrAll dt'' (List.mem_cons_of_mem _ hdt''))
            hStep
      exact hpreserve rest _ hrest_ctor hrest_dt_struct h1
    · -- dt ∈ rest. Use IH on rest.
      have hrest_ctor : ∀ dt' ∈ rest, ∀ c ∈ dt'.constructors,
          dt'.name.pushNamespace c.nameHead ≠ dt.name := by
        intro dt' hdt' c hc
        exact hCtorNotKey dt' (List.mem_cons_of_mem _ hdt') c hc
      have hrest_other : ∀ dt' ∈ rest, dt' ≠ dt → dt'.name ≠ dt.name := by
        intro dt' hdt' hne
        exact hOtherDtNotKey dt' (List.mem_cons_of_mem _ hdt') hne
      exact dtStep_foldl_list_inserts_DtMatchesNH_at_dt_name mono rest
        (dtStep mono init hd) hmem_rest hrest_ctor hrest_other

/-- `dtStep` Array foldl inserts `.dataType` with `DtMatchesNH dt` at `dt.name`
for `dt ∈ newDataTypes`, under disjointness hypotheses. -/
private theorem dtStep_foldl_inserts_DtMatchesNH_at_dt_name
    (mono : MonoMap) (newDataTypes : Array DataType)
    (init : Typed.Decls) {dt : DataType} (hmem : dt ∈ newDataTypes)
    (hDtCtorNotKey : ∀ dt' ∈ newDataTypes, ∀ c ∈ dt'.constructors,
      dt'.name.pushNamespace c.nameHead ≠ dt.name)
    (hOtherDtNotKey : ∀ dt' ∈ newDataTypes, dt' ≠ dt → dt'.name ≠ dt.name) :
    ∃ d, (newDataTypes.foldl (dtStep mono) init).getByKey dt.name = some d ∧
      DtMatchesNH dt d := by
  rw [← Array.foldl_toList]
  have hmem' : dt ∈ newDataTypes.toList := Array.mem_toList_iff.mpr hmem
  have hCtor' : ∀ dt' ∈ newDataTypes.toList, ∀ c ∈ dt'.constructors,
      dt'.name.pushNamespace c.nameHead ≠ dt.name := by
    intro dt' hdt'; exact hDtCtorNotKey dt' (Array.mem_toList_iff.mp hdt')
  have hOther' : ∀ dt' ∈ newDataTypes.toList, dt' ≠ dt → dt'.name ≠ dt.name := by
    intro dt' hdt'; exact hOtherDtNotKey dt' (Array.mem_toList_iff.mp hdt')
  exact dtStep_foldl_list_inserts_DtMatchesNH_at_dt_name mono
    newDataTypes.toList init hmem' hCtor' hOther'

/-- `fnStep` preserves `DtMatchesNH` at `g` under `f.name ≠ g`. -/
private theorem fnStep_preserves_DtMatchesNH
    (decls : Typed.Decls) (mono : MonoMap) (acc : Typed.Decls) (f : Typed.Function)
    (target_dt : DataType)
    {g : Global} (hfn_ne : f.name ≠ g)
    (hacc : ∃ d, acc.getByKey g = some d ∧ DtMatchesNH target_dt d) :
    ∃ d, (fnStep decls mono acc f).getByKey g = some d ∧
      DtMatchesNH target_dt d := by
  unfold fnStep
  have hbeq : (f.name == g) = false := by
    rw [beq_eq_false_iff_ne]; exact hfn_ne
  obtain ⟨d, hget, hM⟩ := hacc
  refine ⟨d, ?_, hM⟩
  rw [IndexMap.getByKey_insert_of_beq_false _ _ hbeq]
  exact hget

/-- `fnStep` Array foldl preserves `DtMatchesNH` at `g` under `hFnNotKey`. -/
private theorem fnStep_foldl_preserves_DtMatchesNH
    (decls : Typed.Decls) (mono : MonoMap) (newFunctions : Array Typed.Function)
    (init : Typed.Decls) (target_dt : DataType) {g : Global}
    (hinit : ∃ d, init.getByKey g = some d ∧ DtMatchesNH target_dt d)
    (hFnNotKey : ∀ f ∈ newFunctions, f.name ≠ g) :
    ∃ d, (newFunctions.foldl (fnStep decls mono) init).getByKey g = some d ∧
      DtMatchesNH target_dt d := by
  apply Array.foldl_induction
    (motive := fun (_ : Nat) (acc : Typed.Decls) =>
      ∃ d, acc.getByKey g = some d ∧ DtMatchesNH target_dt d) hinit
  intro i acc hinv
  have hfn_ne : (newFunctions[i.val]'i.isLt).name ≠ g :=
    hFnNotKey _ (Array.getElem_mem _)
  exact fnStep_preserves_DtMatchesNH decls mono acc _ target_dt hfn_ne hinv

/-- Explicit-structure version of `concretizeBuild_at_newDt_name`: under the
disjointness hypotheses + uniqueness within `newDataTypes` (any other newDt
with the same name as `dt` is structurally equal to `dt`), the
`concretizeBuild` result at `dt.name` carries `DtMatchesNH dt` (length and
per-position nameHead correspondence with `dt`'s constructors). -/
private theorem concretizeBuild_at_newDt_name_explicit
    (typedDecls : Typed.Decls) (mono : MonoMap)
    (newFunctions : Array Typed.Function) (newDataTypes : Array DataType)
    {dt : DataType} (hmem : dt ∈ newDataTypes)
    (hDtCtorNotKey : ∀ dt' ∈ newDataTypes, ∀ c ∈ dt'.constructors,
      dt'.name.pushNamespace c.nameHead ≠ dt.name)
    (hFnNotKey : ∀ f ∈ newFunctions, f.name ≠ dt.name)
    (hOtherDtNotKey : ∀ dt' ∈ newDataTypes, dt' ≠ dt → dt'.name ≠ dt.name) :
    ∃ md_dt,
      (concretizeBuild typedDecls mono newFunctions newDataTypes).getByKey dt.name =
        some (.dataType md_dt) ∧
      md_dt.constructors.length = dt.constructors.length ∧
      (∀ i (hi : i < dt.constructors.length)
          (hi' : i < md_dt.constructors.length),
        (md_dt.constructors[i]'hi').nameHead = (dt.constructors[i]'hi).nameHead) := by
  rw [concretizeBuild_eq]
  have h2 := dtStep_foldl_inserts_DtMatchesNH_at_dt_name mono newDataTypes
    (typedDecls.pairs.foldl (srcStep typedDecls mono) default) hmem hDtCtorNotKey
    hOtherDtNotKey
  have h3 := fnStep_foldl_preserves_DtMatchesNH typedDecls mono newFunctions _
    dt h2 hFnNotKey
  obtain ⟨d, hget, hM⟩ := h3
  obtain ⟨md_dt, hd_eq, hLen, hPos⟩ := hM
  refine ⟨md_dt, ?_, hLen, hPos⟩
  rw [hget, hd_eq]

end PhaseA2

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

/-! ### PLAN_3B Phase B prerequisites: reverse kind correspondence + ctorIdx +
dtSize agreement. Each is a precisely-named sub-sorry; closed in subsequent
sessions per PLAN_3B.md S5-S7. -/

/-- Helper: `step4Lower` foldlM preserves "no key g" when monoDecls has none at g. -/
private theorem step4Lower_fold_preserves_none_at_key
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
private theorem step4Lower_backward_dataType_kind_at_key
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
private theorem step4Lower_backward_function_kind_at_key
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
private theorem step4Lower_backward_ctor_kind_at_key
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

/-- Helper: under `∃ f ∈ newFunctions, f.name = g`, `fnStep` foldl ends with
`.function` at `g` (every fnStep insert at f.name produces `.function`). -/
private theorem fnStep_foldl_with_fname_yields_function
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
  obtain ⟨cd_dt', cd_c', hcd', hLen_cd, hNH_cd, hPos_cd, hStruct_cd⟩ :=
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

/-! #### Phase C scaffolding (F=0): per-`Typ` flat-size correspondence.

The dataType-level theorem `concretize_under_fullymono_dt_flat_size_agree`
factors through a per-`Typ` correspondence: for any source `Typ` and the
`Concrete.Typ` it concretizes to (via `typToConcrete ∘ rewriteTyp emptySubst
drained.mono`, which under `FullyMonomorphic` collapses since args = #[]),
`typFlatSize decls {} ty = Concrete.typFlatSize concDecls {} cty`.

The scaffolding here defines:
1. `Source.Typ.MatchesConcreteFM` — an inductive relation capturing the
   structural shape produced by the FullyMono-reduced concretize composition.
   Under FullyMono args = #[] always, so `.app g #[]` collapses to `.ref g`
   (since `concretizeName g #[] = g`, both `rewriteTyp` and `typToConcrete`
   produce `.ref g`).
2. `Source.Decls.DeclsAgreeOnDtFM` — captures decls-level data-type agreement:
   for any `g` with `.dataType` on both sides, constructor lists have the same
   length and each positional argType is related by `MatchesConcreteFM`.
3. Fuel-zero base lemma — proven (both sides return 0 at fuel 0 for non-dt
   typs; dt-side returns 1 at fuel 0).
4. Leaf-arm lemma — non-recursive arms (unit/field/pointer/function/mvar)
   evaluate to closed-form constants matching their concrete counterparts.

The full mutual-induction theorem (induction on fuel + structural Typ + dt)
remains future work; its statement is captured in the `TypFlatSizeAgreeFM`
predicate below for downstream consumers to cite. -/

/-- Structural relation between source `Typ` and `Concrete.Typ` capturing the
post-`concretize` shape under `FullyMonomorphic`. Under FullyMono args = #[]
always, so `.app` collapses to `.ref`. -/
inductive Typ.MatchesConcreteFM : Typ → Concrete.Typ → Prop
  | unit : MatchesConcreteFM .unit .unit
  | field : MatchesConcreteFM .field .field
  | pointer {t : Typ} {ct : Concrete.Typ} :
      MatchesConcreteFM t ct → MatchesConcreteFM (.pointer t) (.pointer ct)
  | tuple {ts : Array Typ} {cts : Array Concrete.Typ} :
      ts.size = cts.size →
      (∀ i (h₁ : i < ts.size) (h₂ : i < cts.size),
        MatchesConcreteFM (ts[i]'h₁) (cts[i]'h₂)) →
      MatchesConcreteFM (.tuple ts) (.tuple cts)
  | array {t : Typ} {ct : Concrete.Typ} {n : Nat} :
      MatchesConcreteFM t ct →
      MatchesConcreteFM (.array t n) (.array ct n)
  /-- Source `.ref g` maps to concrete `.ref g`. -/
  | ref {g : Global} : MatchesConcreteFM (.ref g) (.ref g)
  /-- Source `.app g #[]` collapses to concrete `.ref g` under FullyMono. -/
  | appEmpty {g : Global} : MatchesConcreteFM (.app g #[]) (.ref g)
  | function {ins : List Typ} {out : Typ}
      {cins : List Concrete.Typ} {cout : Concrete.Typ} :
      ins.length = cins.length →
      (∀ i (h₁ : i < ins.length) (h₂ : i < cins.length),
        MatchesConcreteFM (ins[i]'h₁) (cins[i]'h₂)) →
      MatchesConcreteFM out cout →
      MatchesConcreteFM (.function ins out) (.function cins cout)

/-- Decls-level agreement under FullyMono: for any `g` that resolves to a
`.dataType` on both sides, the constructor lists match positionally with each
arg-type pair related by `MatchesConcreteFM`. Captures the structural fact
established by `concretize_under_fullymono_preserves_dataType_kind_fwd` +
positional ctor correspondence (Phase A.2/A.3 + Phase B). -/
def Source.Decls.DeclsAgreeOnDtFM
    (decls : Source.Decls) (concDecls : Concrete.Decls) : Prop :=
  ∀ (g : Global) (src_dt : DataType) (cd_dt : Concrete.DataType),
    decls.getByKey g = some (.dataType src_dt) →
    concDecls.getByKey g = some (.dataType cd_dt) →
    src_dt.constructors.length = cd_dt.constructors.length ∧
    (∀ i (h₁ : i < src_dt.constructors.length)
       (h₂ : i < cd_dt.constructors.length),
      let src_c := src_dt.constructors[i]'h₁
      let cd_c := cd_dt.constructors[i]'h₂
      src_c.argTypes.length = cd_c.argTypes.length ∧
      ∀ j (hj₁ : j < src_c.argTypes.length) (hj₂ : j < cd_c.argTypes.length),
        Typ.MatchesConcreteFM (src_c.argTypes[j]'hj₁)
                              (cd_c.argTypes[j]'hj₂))

/-- Fuel-zero base case: both `typFlatSizeBound` and `Concrete.typFlatSizeBound`
return `0` at fuel `0`. F=0 leaf. -/
private theorem typFlatSizeBound_zero_eq
    (decls : Source.Decls) (cd : Concrete.Decls)
    (visited : Std.HashSet Global) (visited' : Std.HashSet Global)
    (ty : Typ) (cty : Concrete.Typ) :
    typFlatSizeBound decls 0 visited ty =
      Concrete.typFlatSizeBound cd 0 visited' cty := by
  unfold typFlatSizeBound Concrete.typFlatSizeBound
  rfl

/-- Fuel-zero base case for `dataTypeFlatSizeBound`: both sides return `1`. -/
private theorem dataTypeFlatSizeBound_zero_eq
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
private theorem typFlatSizeBound_leaf_unit
    (decls : Source.Decls) (cd : Concrete.Decls) (n : Nat)
    (V : Std.HashSet Global) (V' : Std.HashSet Global) :
    typFlatSizeBound decls (n+1) V .unit =
      Concrete.typFlatSizeBound cd (n+1) V' .unit := by
  unfold typFlatSizeBound Concrete.typFlatSizeBound
  rfl

private theorem typFlatSizeBound_leaf_field
    (decls : Source.Decls) (cd : Concrete.Decls) (n : Nat)
    (V : Std.HashSet Global) (V' : Std.HashSet Global) :
    typFlatSizeBound decls (n+1) V .field =
      Concrete.typFlatSizeBound cd (n+1) V' .field := by
  unfold typFlatSizeBound Concrete.typFlatSizeBound
  rfl

private theorem typFlatSizeBound_leaf_pointer
    (decls : Source.Decls) (cd : Concrete.Decls) (n : Nat)
    (V : Std.HashSet Global) (V' : Std.HashSet Global)
    (t : Typ) (ct : Concrete.Typ) :
    typFlatSizeBound decls (n+1) V (.pointer t) =
      Concrete.typFlatSizeBound cd (n+1) V' (.pointer ct) := by
  unfold typFlatSizeBound Concrete.typFlatSizeBound
  rfl

private theorem typFlatSizeBound_leaf_function
    (decls : Source.Decls) (cd : Concrete.Decls) (n : Nat)
    (V : Std.HashSet Global) (V' : Std.HashSet Global)
    (ins : List Typ) (out : Typ)
    (cins : List Concrete.Typ) (cout : Concrete.Typ) :
    typFlatSizeBound decls (n+1) V (.function ins out) =
      Concrete.typFlatSizeBound cd (n+1) V' (.function cins cout) := by
  unfold typFlatSizeBound Concrete.typFlatSizeBound
  rfl

/-- Phase C main: dataType flat-size agreement under FullyMono.
BLOCKED ON: per-Typ flat-size correspondence (`TypFlatSizeAgreeFM` predicate
above) via `Typ.instantiate_empty_id` + typToConcrete preservation. ~150 LoC. -/
theorem concretize_under_fullymono_dt_flat_size_agree
    {t : Source.Toplevel} {decls : Source.Decls}
    {typedDecls : Typed.Decls} {concDecls : Concrete.Decls}
    (_hmono : FullyMonomorphic t)
    (_hdecls : t.mkDecls = .ok decls)
    (_hts : t.checkAndSimplify = .ok typedDecls)
    (_hconc : typedDecls.concretize = .ok concDecls)
    {g : Global}
    {src_dt : DataType} {src_c : Constructor}
    {cd_dt : Concrete.DataType} {cd_c : Concrete.Constructor}
    (_hsrc : decls.getByKey g = some (.constructor src_dt src_c))
    (_hcd : concDecls.getByKey g = some (.constructor cd_dt cd_c)) :
    dataTypeFlatSize decls {} src_dt =
      Concrete.dataTypeFlatSize concDecls {} cd_dt := by
  sorry

-- Phase D wiring: dispatches on source/concrete kind, uses Phase A.4 + B + C.
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
  | .unit        => by unfold flattenValue Concrete.flattenValue; rfl
  | .field _     => by unfold flattenValue Concrete.flattenValue; rfl
  | .pointer _ _ => by unfold flattenValue Concrete.flattenValue; rfl
  | .fn _        => by unfold flattenValue Concrete.flattenValue; rfl
  | .tuple vs    => by
      unfold flattenValue Concrete.flattenValue
      exact flatten_attach_flatMap_eq_pw
        (fun v _ => flatten_agree_under_fullymono _hmono _hdecls _hts _hconc funcIdx v)
  | .array vs    => by
      unfold flattenValue Concrete.flattenValue
      exact flatten_attach_flatMap_eq_pw
        (fun v _ => flatten_agree_under_fullymono _hmono _hdecls _hts _hconc funcIdx v)
  | .ctor g args => by
      unfold flattenValue Concrete.flattenValue
      have h_args : args.attach.flatMap (fun ⟨v, _⟩ => flattenValue decls funcIdx v) =
                    args.attach.flatMap
                      (fun ⟨v, _⟩ => Concrete.flattenValue concDecls funcIdx v) :=
        flatten_attach_flatMap_eq_pw
          (fun v _ => flatten_agree_under_fullymono _hmono _hdecls _hts _hconc funcIdx v)
      cases hsrc : decls.getByKey g with
      | none =>
        cases hcd : concDecls.getByKey g with
        | none => exact h_args
        | some d_cd =>
          cases d_cd with
          | constructor cd_dt cd_c =>
            exfalso
            obtain ⟨_, _, hsrc'⟩ :=
              concretize_under_fullymono_preserves_ctor_kind_bwd
                _hmono _hdecls _hts _hconc hcd
            rw [hsrc] at hsrc'; cases hsrc'
          | _ => exact h_args
      | some d_src =>
        cases d_src with
        | function _ =>
          cases hcd : concDecls.getByKey g with
          | none => exact h_args
          | some d_cd =>
            cases d_cd with
            | constructor cd_dt cd_c =>
              exfalso
              obtain ⟨_, _, hsrc'⟩ :=
                concretize_under_fullymono_preserves_ctor_kind_bwd
                  _hmono _hdecls _hts _hconc hcd
              rw [hsrc] at hsrc'; cases hsrc'
            | _ => exact h_args
        | dataType _ =>
          cases hcd : concDecls.getByKey g with
          | none => exact h_args
          | some d_cd =>
            cases d_cd with
            | constructor cd_dt cd_c =>
              exfalso
              obtain ⟨_, _, hsrc'⟩ :=
                concretize_under_fullymono_preserves_ctor_kind_bwd
                  _hmono _hdecls _hts _hconc hcd
              rw [hsrc] at hsrc'; cases hsrc'
            | _ => exact h_args
        | constructor src_dt src_c =>
          obtain ⟨cd_dt, cd_c, hcd⟩ :=
            concretize_under_fullymono_preserves_ctor_kind_fwd
              _hmono _hdecls _hts _hconc hsrc
          have hidx := concretize_under_fullymono_ctor_idx_agree
            _hmono _hdecls _hts _hconc hsrc hcd
          have hsize := concretize_under_fullymono_dt_flat_size_agree
            _hmono _hdecls _hts _hconc hsrc hcd
          simp only [hsrc, hcd]
          rw [hidx, hsize, h_args]
  termination_by v => sizeOf v
  decreasing_by all_goals (have := Array.sizeOf_lt_of_mem ‹_ ∈ _›; grind)

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
private def _l1_docstub : Unit := ()

/-- Transport a source-side `SrcTypRefsAreDtKeys` witness to a typed-side
`TypRefsAreDtKeys` witness, given that every `.dataType`-at-key in source
decls survives to a `.dataType`-at-key in typed decls (via
`checkAndSimplify_src_dt_to_td`). -/
private theorem TypRefsAreDtKeys_of_SrcTypRefsAreDtKeys
    {t : Source.Toplevel} {decls : Source.Decls} {tds : Typed.Decls}
    (hdecls : t.mkDecls = .ok decls)
    (hts : t.checkAndSimplify = .ok tds) :
    ∀ (τ : Typ), SrcTypRefsAreDtKeys decls τ → TypRefsAreDtKeys tds τ
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
private theorem L1_dt_and_ctor_arms
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
    have hSrc := SrcTypRefsAreDtKeys_of_wellFormedType decls ty hty_wf
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
    have hSrc := SrcTypRefsAreDtKeys_of_wellFormedType decls ty hty_wf
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
      have hSrc := SrcTypRefsAreDtKeys_of_wellFormedType decls lt.2 hlt_wf
      exact TypRefsAreDtKeys_of_SrcTypRefsAreDtKeys hdecls hts lt.2 hSrc
    · rw [houtput]
      have hSrc := SrcTypRefsAreDtKeys_of_wellFormedType decls fsrc.output houtput_ok
      exact TypRefsAreDtKeys_of_SrcTypRefsAreDtKeys hdecls hts fsrc.output hSrc
  | dataType dt =>
    subst hd
    exact hDtArm name dt hget_td
  | constructor dt c =>
    subst hd
    exact hCtorArm name dt c hget_td

/-! #### L2: every tds dt-key survives to cd. -/

/-- Default `Typed.Decls` returns `none` on any `getByKey`. -/
private theorem default_typedDecls_getByKey_none (g : Global) :
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
private theorem L2_phase1_fromSource
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
private theorem L2_phase2_withNewDts
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
private theorem L2_phase3_newFunctions
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
private theorem typToConcrete_preserves_RefTargetsInTds
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

/-- Step-wise invariant: if the accumulator satisfies `AllRefsTargetTds` AND
the next input `d_mono`'s types all satisfy `TypNoAppRefDtKey tds`, then the
post-step4Lower accumulator satisfies `AllRefsTargetTds`. -/
private theorem step4Lower_preserves_AllRefsTargetTds
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
private theorem step4Lower_foldlM_preserves_AllRefsTargetTds
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
private theorem rewriteTyp_preserves_TypNoAppRefDtKey
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
private theorem typOkForRewrite_of_apps_in_seen
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

private def DrainState.NewDeclTypesRefsOk (tds : Typed.Decls) (st : DrainState) : Prop :=
  (∀ dt ∈ st.newDataTypes, ∀ c ∈ dt.constructors, ∀ ty ∈ c.argTypes,
      TypRefsAreDtKeys tds ty) ∧
  (∀ f ∈ st.newFunctions,
      (∀ lt ∈ f.inputs, TypRefsAreDtKeys tds lt.snd) ∧
      TypRefsAreDtKeys tds f.output)

private theorem DrainState.NewDeclTypesRefsOk.init {tds : Typed.Decls}
    (pending : Std.HashSet (Global × Array Typ)) :
    DrainState.NewDeclTypesRefsOk tds
      { pending, seen := {}, mono := {}, newFunctions := #[], newDataTypes := #[] } := by
  refine ⟨?_, ?_⟩
  · intro dt hdt; simp only [Array.not_mem_empty] at hdt
  · intro f hf; simp only [Array.not_mem_empty] at hf

private theorem concretizeDrainEntry_preserves_NewDeclTypesRefsOk
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

private theorem concretizeDrainEntry_list_foldlM_preserves_NewDeclTypesRefsOk
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

private theorem concretizeDrainIter_preserves_NewDeclTypesRefsOk
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

private theorem concretize_drain_preserves_NewDeclTypesRefsOk
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
private theorem drainMono_coversTypesInTds
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
private theorem concretizeBuild_phase1_preserves_noAppRefDtKey
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
private theorem concretizeBuild_phase2_preserves_noAppRefDtKey
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
private theorem concretizeBuild_phase3_preserves_noAppRefDtKey
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
private theorem monoDecls_types_noAppRefDtKey
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
private theorem refTargetsInTds_to_refClosed
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

-- `Typed.Typ.ParamSafe` and `Typed.Decls.NoDirectDatatypeCycles` now live
-- in `Ix.Aiur.Semantics.WellFormed` so the `WellFormed` obligation can reference
-- them.

/-! ### Decomposition of `concretize_produces_sizeBoundOk`.

Candidate encoding for `NoDirectDatatypeCycles`: there exists
`rank : Global → Nat` such that every `.ref g'` appearing in the
non-`.pointer` spine of a datatype keyed `g` satisfies `rank g' < rank g`.
This is what `WellFormed` should imply once it's made precise. -/

-- `Concrete.Typ.SpineRefsBelow` moved to `Ix/Aiur/Semantics/ConcreteInvariants.lean`.

/-- `concretize`'s output inherits a rank-based DAG witness from the source.

**Rank witness**: `rank_cd g := rank_src (origin g)` where `origin g` is the
template name if `g = concretizeName template args` (via mono-map inverse),
or `g` itself if monomorphic-carried.

**Proof plan** (Agent A's analysis):
1. Case-split on whether `g` is a specialization or a monomorphic survivor.
2. For each edge `t = .ref g'` in `cd`, trace back through `typToConcrete` →
   `rewriteTyp` → source template argtype.
3. Edge origin is either:
   (a) source `.ref g'` in template spine (bounded by source `.ref` rank),
   (b) source `.app g' args` (bounded by source `.app` rank, extended field),
   (c) source `.ref p` / `.app p ...` with `p` a param — RULED OUT by
       `Typ.ParamSafe` conjunct in `NoDirectDatatypeCycles`.
4. Rank inequality transfers via the two-case origin construction.

**Latent blocker** (surfaced this session): the rank-witness construction
requires uniqueness of `concretizeName` preimage within `drained.mono` (not
injective globally per the deleted `concretizeName_injective`; may hold
per-drain via the `seen` invariant, but unproved). Without that, multiple
source templates `(g1, a1)`, `(g2, a2)` can map to the same `concName` with
different `rank_src g1` ≠ `rank_src g2` values — ambiguous rank assignment.
An alternative is `rank_cd g := max over preimages rank_src gi`, but then
strictness `rank_cd concName < rank_cd key` fails when the max argmax has
the same rank as the dt whose edge we're tracing.

(Closed 2026-04-24 via ported `DirectDagBody` helpers below.) -/
private def _directDagBody_docstub : Unit := ()

-- Shared helpers (StrongNewNameShape chain + step4Lower helpers) moved before
-- `namespace RefClosedBody` (see earlier in this file) so both `RefClosedBody`
-- and `DirectDagBody` can use them.

namespace DirectDagBody

-- `TemplateOf` def moved to `Ix/Aiur/Semantics/ConcreteInvariants.lean`.

/-! #### `concretizeBuild` shape-at-key analysis.

If the final monoDecls has `.dataType` at key `g`, the LAST writer of that
key's value must have been a `.dataType`-insertion. Two fold steps do so:
`srcStep` with `srcD = .dataType` (params empty), and `dtStep`'s outer insert
at `dt.name`. Either gives a template. -/

/-- Generic `List.foldl` backward dichotomy: either some element has key `g`,
or the fold preserves `getByKey g`. -/
private theorem listFoldl_shape_bwd
    {β : Type _}
    (step : Typed.Decls → β → Typed.Decls)
    (toKey : β → Global)
    (hstep_other : ∀ (acc : Typed.Decls) (b : β) (g' : Global),
      (toKey b == g') = false →
      (step acc b).getByKey g' = acc.getByKey g') :
    ∀ (xs : List β) (init : Typed.Decls) (g : Global),
      (∃ b ∈ xs, toKey b = g) ∨
      (xs.foldl step init).getByKey g = init.getByKey g := by
  intro xs init g
  induction xs generalizing init with
  | nil => right; rfl
  | cons hd tl ih =>
    by_cases hkey : toKey hd = g
    · left; exact ⟨hd, List.mem_cons_self, hkey⟩
    · have hne : (toKey hd == g) = false := by
        rw [beq_eq_false_iff_ne]; exact hkey
      simp only [List.foldl_cons]
      rcases ih (step init hd) with ⟨b, hb, heq⟩ | hpreserve
      · left; exact ⟨b, List.mem_cons_of_mem _ hb, heq⟩
      · right
        rw [hpreserve]
        exact hstep_other init hd g hne

/-- If `∃ b ∈ xs, toKey b = g`, the last such `b`'s insert determines the
value at `g` after `xs.foldl step init`. -/
private theorem listFoldl_last_writer_shape
    {β : Type _}
    (step : Typed.Decls → β → Typed.Decls)
    (toKey : β → Global)
    (hstep_other : ∀ (acc : Typed.Decls) (b : β) (g' : Global),
      (toKey b == g') = false →
      (step acc b).getByKey g' = acc.getByKey g')
    (hstep_kind : ∀ (acc : Typed.Decls) (b : β),
      ∃ d_ins, (step acc b).getByKey (toKey b) = some d_ins) :
    ∀ (xs : List β) (init : Typed.Decls) (g : Global),
      (∃ b ∈ xs, toKey b = g) →
      ∃ d, (xs.foldl step init).getByKey g = some d ∧
        ∃ b ∈ xs, toKey b = g ∧
          ∃ acc_pre, (step acc_pre b).getByKey g = some d := by
  intro xs
  induction xs with
  | nil => intro _ _ ⟨_, hmem, _⟩; cases hmem
  | cons hd tl ih =>
    intro init g ⟨b, hmem, hbeq⟩
    simp only [List.foldl_cons]
    by_cases htl_ex : ∃ b' ∈ tl, toKey b' = g
    · obtain ⟨d, hd_eq, b', hb'mem, hb'eq, acc_pre, hacc_pre⟩ := ih (step init hd) g htl_ex
      exact ⟨d, hd_eq, b', List.mem_cons_of_mem _ hb'mem, hb'eq, acc_pre, hacc_pre⟩
    · rcases List.mem_cons.mp hmem with hbhd | htl
      · subst hbhd
        obtain ⟨d_ins, hd_ins⟩ := hstep_kind init b
        refine ⟨d_ins, ?_, b, List.mem_cons_self, hbeq, init, ?_⟩
        · have htl_preserve : (tl.foldl step (step init b)).getByKey g
              = (step init b).getByKey g := by
            rcases listFoldl_shape_bwd step toKey hstep_other tl (step init b) g with
              ⟨b', hb'mem, hb'eq⟩ | hp
            · exact absurd ⟨b', hb'mem, hb'eq⟩ htl_ex
            · exact hp
          rw [htl_preserve]
          rw [← hbeq]; exact hd_ins
        · rw [← hbeq]; exact hd_ins
      · exact absurd ⟨b, htl, hbeq⟩ htl_ex

/-- For any key `g` with `(concretizeBuild decls mono newFunctions newDataTypes).getByKey g
    = some (.dataType dt_mono)`, one of:
- Source has `.dataType dt_src` at `g` with `dt_src.params = []`, OR
- `∃ dt ∈ newDataTypes, dt.name = g`. -/
private theorem concretizeBuild_dataType_origin
    (decls : Typed.Decls) (mono : MonoMap)
    (newFunctions : Array Typed.Function) (newDataTypes : Array DataType)
    {g : Global} {dt_mono : DataType}
    (hget : (concretizeBuild decls mono newFunctions newDataTypes).getByKey g =
      some (.dataType dt_mono)) :
    (∃ dt_src, decls.getByKey g = some (.dataType dt_src) ∧ dt_src.params = []) ∨
    (∃ dt ∈ newDataTypes, dt.name = g) := by
  let emptySubst : Global → Option Typ := fun _ => none
  let srcStep : Typed.Decls → Global × Typed.Declaration → Typed.Decls :=
    fun acc p =>
      match p.2 with
      | .function f =>
        if f.params.isEmpty then
          acc.insert p.1 (.function
            { f with
              inputs := f.inputs.map fun (l, t) => (l, rewriteTyp emptySubst mono t),
              output := rewriteTyp emptySubst mono f.output,
              body := rewriteTypedTerm decls emptySubst mono f.body })
        else acc
      | .dataType dt =>
        if dt.params.isEmpty then
          let newCtors := dt.constructors.map fun c =>
            { c with argTypes := c.argTypes.map (rewriteTyp emptySubst mono) }
          acc.insert p.1 (.dataType { dt with constructors := newCtors })
        else acc
      | .constructor dt c =>
        if dt.params.isEmpty then
          let newArgTypes := c.argTypes.map (rewriteTyp emptySubst mono)
          let newCtor : Constructor := { c with argTypes := newArgTypes }
          let rewrittenCtors := dt.constructors.map fun c' =>
            { c' with argTypes := c'.argTypes.map (rewriteTyp emptySubst mono) }
          let newDt : DataType := { dt with constructors := rewrittenCtors }
          acc.insert p.1 (.constructor newDt newCtor)
        else acc
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
  let fnStep : Typed.Decls → Typed.Function → Typed.Decls := fun acc f =>
    acc.insert f.name (.function
      { f with
        inputs := f.inputs.map fun (l, t) => (l, rewriteTyp emptySubst mono t),
        output := rewriteTyp emptySubst mono f.output,
        body := rewriteTypedTerm decls emptySubst mono f.body })
  let fromSource := decls.pairs.toList.foldl srcStep default
  let withNewDts := newDataTypes.toList.foldl dtStep fromSource
  have hconc_eq :
      concretizeBuild decls mono newFunctions newDataTypes =
        newFunctions.toList.foldl fnStep withNewDts := by
    show concretizeBuild decls mono newFunctions newDataTypes =
      newFunctions.toList.foldl fnStep
        (newDataTypes.toList.foldl dtStep
          (decls.pairs.toList.foldl srcStep default))
    unfold concretizeBuild
    repeat rw [← Array.foldl_toList]
    rfl
  rw [hconc_eq] at hget
  have hfn_preserves_other : ∀ (acc : Typed.Decls) (f : Typed.Function) (g' : Global),
      (f.name == g') = false →
      (fnStep acc f).getByKey g' = acc.getByKey g' := by
    intro acc f g' hne
    show (acc.insert f.name _).getByKey g' = acc.getByKey g'
    exact IndexMap.getByKey_insert_of_beq_false _ _ hne
  have hfn_kind : ∀ (acc : Typed.Decls) (f : Typed.Function),
      ∃ d_ins, (fnStep acc f).getByKey f.name = some d_ins ∧
        ∃ f_ins, d_ins = .function f_ins := by
    intro acc f
    refine ⟨_, IndexMap.getByKey_insert_self _ _ _, _, rfl⟩
  rcases listFoldl_shape_bwd fnStep Typed.Function.name hfn_preserves_other
    newFunctions.toList withNewDts g with
    hfn_ex | hfn_preserve
  · exfalso
    have hkind_simple : ∀ (acc : Typed.Decls) (f : Typed.Function),
        ∃ d_ins, (fnStep acc f).getByKey f.name = some d_ins := fun acc f =>
      ⟨_, IndexMap.getByKey_insert_self _ _ _⟩
    obtain ⟨d, hd_eq, f_last, _, hf_last_key, acc_pre, hacc_pre⟩ :=
      listFoldl_last_writer_shape fnStep Typed.Function.name hfn_preserves_other
        hkind_simple newFunctions.toList withNewDts g hfn_ex
    rw [hd_eq] at hget
    have hins_val : (fnStep acc_pre f_last).getByKey g = some (.function
        { f_last with
          inputs := f_last.inputs.map fun (l, t) => (l, rewriteTyp emptySubst mono t),
          output := rewriteTyp emptySubst mono f_last.output,
          body := rewriteTypedTerm decls emptySubst mono f_last.body }) := by
      show (acc_pre.insert f_last.name _).getByKey g = some _
      rw [← hf_last_key]
      exact IndexMap.getByKey_insert_self _ _ _
    rw [hins_val] at hacc_pre
    simp only [Option.some.injEq] at hacc_pre
    rw [← hacc_pre] at hget
    cases hget
  · rw [hfn_preserve] at hget
    by_cases hdt_ex : ∃ dt ∈ newDataTypes.toList, dt.name = g
    · obtain ⟨dt, hdtmem, hdteq⟩ := hdt_ex
      exact Or.inr ⟨dt, Array.mem_toList_iff.mp hdtmem, hdteq⟩
    · have hdt_pres_lemma : ∀ (xs : List DataType) (init : Typed.Decls),
            (∀ dt ∈ xs, dt.name ≠ g) →
            (∀ dt ∈ xs, ∀ c ∈ dt.constructors,
              dt.name.pushNamespace c.nameHead ≠ g) →
            (xs.foldl dtStep init).getByKey g = init.getByKey g := by
          intro xs
          induction xs with
          | nil => intros; rfl
          | cons hd tl ih =>
            intro init hno_dt hno_ctor
            simp only [List.foldl_cons]
            have hnd_name : hd.name ≠ g := hno_dt hd List.mem_cons_self
            have hnd_ctor : ∀ c ∈ hd.constructors,
                hd.name.pushNamespace c.nameHead ≠ g :=
              fun c hc => hno_ctor hd List.mem_cons_self c hc
            have ih_tl := ih (dtStep init hd)
              (fun dt hdt => hno_dt dt (List.mem_cons_of_mem _ hdt))
              (fun dt hdt c hc => hno_ctor dt (List.mem_cons_of_mem _ hdt) c hc)
            rw [ih_tl]
            have hnd_beq : (hd.name == g) = false := by
              rw [beq_eq_false_iff_ne]; exact hnd_name
            have h_inner : ∀ (cs : List Constructor) (acc' : Typed.Decls)
                (_hne_cs : ∀ c ∈ cs, hd.name.pushNamespace c.nameHead ≠ g)
                (body : Constructor → Typed.Declaration),
                IndexMap.getByKey (cs.foldl (fun acc'' c =>
                  acc''.insert (hd.name.pushNamespace c.nameHead) (body c)) acc') g
                = acc'.getByKey g := by
              intro cs
              induction cs with
              | nil => intros; rfl
              | cons c0 rest ih_cs =>
                intro acc' hne body
                simp only [List.foldl_cons]
                have hnc0 : hd.name.pushNamespace c0.nameHead ≠ g :=
                  hne c0 List.mem_cons_self
                have hnc0_beq : (hd.name.pushNamespace c0.nameHead == g) = false := by
                  rw [beq_eq_false_iff_ne]; exact hnc0
                have := ih_cs (acc'.insert (hd.name.pushNamespace c0.nameHead) (body c0))
                  (fun c' hc' => hne c' (List.mem_cons_of_mem _ hc')) body
                rw [this]
                exact IndexMap.getByKey_insert_of_beq_false _ _ hnc0_beq
            have hnd_ctor_rw : ∀ c ∈ (hd.constructors.map fun c =>
                { c with argTypes := c.argTypes.map (rewriteTyp emptySubst mono) }),
                hd.name.pushNamespace c.nameHead ≠ g := by
              intro c' hc'
              simp only [List.mem_map] at hc'
              obtain ⟨c0, hc0, hc0_eq⟩ := hc'
              rw [← hc0_eq]
              exact hnd_ctor c0 hc0
            rw [h_inner _ _ hnd_ctor_rw _]
            exact IndexMap.getByKey_insert_of_beq_false _ _ hnd_beq
      by_cases hctor_ex : ∃ dt ∈ newDataTypes.toList,
          ∃ c ∈ dt.constructors, dt.name.pushNamespace c.nameHead = g
      · exfalso
        have hkey_lemma :
            ∀ (xs : List DataType) (init : Typed.Decls),
              (∀ dt ∈ xs, dt.name ≠ g) →
              (∃ dt ∈ xs, ∃ c ∈ dt.constructors,
                dt.name.pushNamespace c.nameHead = g) →
              ∃ cdt cc, (xs.foldl dtStep init).getByKey g
                = some (.constructor cdt cc) := by
          intro xs
          induction xs with
          | nil =>
            intro _ _ ⟨_, hm, _⟩; cases hm
          | cons hd tl ih =>
            intro init hno_dt hex
            simp only [List.foldl_cons]
            by_cases htl_ex : ∃ dt ∈ tl, ∃ c ∈ dt.constructors,
                dt.name.pushNamespace c.nameHead = g
            · exact ih _ (fun dt hdt => hno_dt dt (List.mem_cons_of_mem _ hdt)) htl_ex
            · obtain ⟨dt_ex, hdt_ex_mem, c_ex, hc_ex_mem, hc_ex_eq⟩ := hex
              have hdt_is_hd : dt_ex = hd := by
                rcases List.mem_cons.mp hdt_ex_mem with rfl | htl_mem
                · rfl
                · exact absurd ⟨dt_ex, htl_mem, c_ex, hc_ex_mem, hc_ex_eq⟩ htl_ex
              subst hdt_is_hd
              have hno_dt_tl : ∀ dt' ∈ tl, dt'.name ≠ g :=
                fun dt' hdt' => hno_dt dt' (List.mem_cons_of_mem _ hdt')
              have hno_ctor_tl : ∀ dt' ∈ tl, ∀ c' ∈ dt'.constructors,
                  dt'.name.pushNamespace c'.nameHead ≠ g := by
                intro dt' hdt' c' hc' heq
                exact htl_ex ⟨dt', hdt', c', hc', heq⟩
              rw [hdt_pres_lemma tl _ hno_dt_tl hno_ctor_tl]
              have hdt_ex_name_ne : dt_ex.name ≠ g :=
                hno_dt dt_ex List.mem_cons_self
              have hctor_ex_rw_dt : ∃ c' ∈ dt_ex.constructors.map fun c =>
                  { c with argTypes := c.argTypes.map (rewriteTyp emptySubst mono) },
                  dt_ex.name.pushNamespace c'.nameHead = g := by
                refine ⟨{ c_ex with argTypes := c_ex.argTypes.map (rewriteTyp emptySubst mono) },
                  ?_, hc_ex_eq⟩
                rw [List.mem_map]
                exact ⟨c_ex, hc_ex_mem, rfl⟩
              have hctor_fold : ∀ (cs : List Constructor) (acc' : Typed.Decls)
                  (rdt : DataType),
                  (∃ c' ∈ cs, dt_ex.name.pushNamespace c'.nameHead = g) →
                  ∃ cdt cc, (cs.foldl (fun acc'' c' =>
                    acc''.insert (dt_ex.name.pushNamespace c'.nameHead)
                      (.constructor rdt c')) acc').getByKey g
                    = some (.constructor cdt cc) := by
                intro cs
                induction cs with
                | nil => intro _ _ ⟨_, hm, _⟩; cases hm
                | cons c0 rest ih_cs =>
                  intro acc' rdt hex_cs
                  simp only [List.foldl_cons]
                  by_cases hrest_ex : ∃ c' ∈ rest,
                      dt_ex.name.pushNamespace c'.nameHead = g
                  · exact ih_cs _ rdt hrest_ex
                  · obtain ⟨c_last, hc_last_mem, hc_last_eq⟩ := hex_cs
                    have hc_last_is_c0 : c_last = c0 := by
                      rcases List.mem_cons.mp hc_last_mem with rfl | hrest_mem
                      · rfl
                      · exact absurd ⟨c_last, hrest_mem, hc_last_eq⟩ hrest_ex
                    subst hc_last_is_c0
                    have hrest_pres : ∀ (xs : List Constructor) (init' : Typed.Decls),
                        (∀ c' ∈ xs, dt_ex.name.pushNamespace c'.nameHead ≠ g) →
                        IndexMap.getByKey (xs.foldl (fun acc'' c' =>
                          acc''.insert (dt_ex.name.pushNamespace c'.nameHead)
                            (.constructor rdt c')) init') g = init'.getByKey g := by
                      intro xs
                      induction xs with
                      | nil => intros; rfl
                      | cons c1 rest' ih_r =>
                        intro init' hne_all
                        simp only [List.foldl_cons]
                        have hnc1 : dt_ex.name.pushNamespace c1.nameHead ≠ g :=
                          hne_all c1 List.mem_cons_self
                        have hnc1_beq :
                            (dt_ex.name.pushNamespace c1.nameHead == g) = false := by
                          rw [beq_eq_false_iff_ne]; exact hnc1
                        rw [ih_r _ (fun c'' hc'' =>
                          hne_all c'' (List.mem_cons_of_mem _ hc''))]
                        exact IndexMap.getByKey_insert_of_beq_false _ _ hnc1_beq
                    have hrest_ne : ∀ c' ∈ rest,
                        dt_ex.name.pushNamespace c'.nameHead ≠ g := by
                      intro c' hc' heq
                      exact hrest_ex ⟨c', hc', heq⟩
                    rw [hrest_pres rest _ hrest_ne]
                    refine ⟨rdt, c_last, ?_⟩
                    rw [← hc_last_eq]
                    exact IndexMap.getByKey_insert_self _ _ _
              exact hctor_fold _ _ _ hctor_ex_rw_dt
        have hno_dt_name : ∀ dt ∈ newDataTypes.toList, dt.name ≠ g := by
          intro dt hdt heq
          exact hdt_ex ⟨dt, hdt, heq⟩
        obtain ⟨cdt_v, cc_v, hfinal⟩ :=
          hkey_lemma newDataTypes.toList fromSource hno_dt_name hctor_ex
        rw [hfinal] at hget
        cases hget
      · have hno_dt_name : ∀ dt ∈ newDataTypes.toList, dt.name ≠ g := by
          intro dt hdt heq
          exact hdt_ex ⟨dt, hdt, heq⟩
        have hno_ctor : ∀ dt ∈ newDataTypes.toList, ∀ c ∈ dt.constructors,
            dt.name.pushNamespace c.nameHead ≠ g := by
          intro dt hdt c hc heq
          exact hctor_ex ⟨dt, hdt, c, hc, heq⟩
        rw [hdt_pres_lemma newDataTypes.toList fromSource hno_dt_name hno_ctor] at hget
        show (∃ dt_src, decls.getByKey g = some (.dataType dt_src) ∧ dt_src.params = []) ∨ _
        have hsrc_shape : ∀ (pairs : List (Global × Typed.Declaration))
            (init : Typed.Decls),
            (∀ p ∈ pairs, decls.getByKey p.1 = some p.2) →
            (pairs.foldl srcStep init).getByKey g = some (.dataType dt_mono) →
            (∃ dt_src, decls.getByKey g = some (.dataType dt_src)
              ∧ dt_src.params = []) ∨
            init.getByKey g = some (.dataType dt_mono) := by
          intro pairs
          induction pairs with
          | nil =>
            intro init _ hfold
            right; exact hfold
          | cons hd tl ih =>
            intro init hpairs hfold
            simp only [List.foldl_cons] at hfold
            have hpairs_tl : ∀ p ∈ tl, decls.getByKey p.1 = some p.2 :=
              fun p hp => hpairs p (List.mem_cons_of_mem _ hp)
            have hpairs_hd : decls.getByKey hd.1 = some hd.2 := hpairs hd List.mem_cons_self
            rcases ih (srcStep init hd) hpairs_tl hfold with hleft | hmid
            · exact Or.inl hleft
            · obtain ⟨k, dd⟩ := hd
              simp only at hmid hpairs_hd
              cases dd with
              | function f =>
                by_cases hp : f.params.isEmpty = true
                · simp only [srcStep, hp, if_true] at hmid
                  by_cases hk : (k == g) = true
                  · have hkeq : k = g := LawfulBEq.eq_of_beq hk
                    rw [hkeq] at hmid
                    rw [IndexMap.getByKey_insert_self] at hmid
                    cases hmid
                  · have hk' : (k == g) = false := Bool.not_eq_true _ |>.mp hk
                    rw [IndexMap.getByKey_insert_of_beq_false _ _ hk'] at hmid
                    exact Or.inr hmid
                · simp only [srcStep, hp, if_false, Bool.false_eq_true] at hmid
                  exact Or.inr hmid
              | dataType dt =>
                by_cases hp : dt.params.isEmpty = true
                · simp only [srcStep, hp, if_true] at hmid
                  by_cases hk : (k == g) = true
                  · have hkeq : k = g := LawfulBEq.eq_of_beq hk
                    refine Or.inl ⟨dt, ?_, ?_⟩
                    · rw [← hkeq]; exact hpairs_hd
                    · cases hdp : dt.params with
                      | nil => rfl
                      | cons _ _ => rw [hdp] at hp; cases hp
                  · have hk' : (k == g) = false := Bool.not_eq_true _ |>.mp hk
                    rw [IndexMap.getByKey_insert_of_beq_false _ _ hk'] at hmid
                    exact Or.inr hmid
                · simp only [srcStep, hp, if_false, Bool.false_eq_true] at hmid
                  exact Or.inr hmid
              | constructor dt c =>
                by_cases hp : dt.params.isEmpty = true
                · simp only [srcStep, hp, if_true] at hmid
                  by_cases hk : (k == g) = true
                  · have hkeq : k = g := LawfulBEq.eq_of_beq hk
                    rw [hkeq] at hmid
                    rw [IndexMap.getByKey_insert_self] at hmid
                    cases hmid
                  · have hk' : (k == g) = false := Bool.not_eq_true _ |>.mp hk
                    rw [IndexMap.getByKey_insert_of_beq_false _ _ hk'] at hmid
                    exact Or.inr hmid
                · simp only [srcStep, hp, if_false, Bool.false_eq_true] at hmid
                  exact Or.inr hmid
        have hdefault_none : (default : Typed.Decls).getByKey g = none := by
          unfold IndexMap.getByKey
          show ((default : Typed.Decls).indices[g]?).bind _ = none
          have : (default : Typed.Decls).indices[g]? = none := by
            show ((default : Std.HashMap Global Nat))[g]? = none
            exact Std.HashMap.getElem?_empty
          rw [this]; rfl
        have hpairs_hyp : ∀ p ∈ decls.pairs.toList, decls.getByKey p.1 = some p.2 := by
          intro p hp
          rcases p with ⟨a, b⟩
          exact IndexMap.getByKey_of_mem_pairs _ _ _ hp
        rcases hsrc_shape decls.pairs.toList default hpairs_hyp hget with hleft | hmid
        · exact Or.inl hleft
        · rw [hdefault_none] at hmid
          cases hmid

/-- For any key `g` with `(concretizeBuild decls mono newFunctions newDataTypes).getByKey g
    = some (.function f_mono)`, one of:
- Source has `.function f_src` at `g` with `f_src.params = []`, OR
- `∃ f ∈ newFunctions, f.name = g`. -/
private theorem concretizeBuild_function_origin
    (decls : Typed.Decls) (mono : MonoMap)
    (newFunctions : Array Typed.Function) (newDataTypes : Array DataType)
    {g : Global} {f_mono : Typed.Function}
    (hget : (concretizeBuild decls mono newFunctions newDataTypes).getByKey g =
      some (.function f_mono)) :
    (∃ f_src, decls.getByKey g = some (.function f_src) ∧ f_src.params = []) ∨
    (∃ f ∈ newFunctions, f.name = g) := by
  let emptySubst : Global → Option Typ := fun _ => none
  let srcStep : Typed.Decls → Global × Typed.Declaration → Typed.Decls :=
    fun acc p =>
      match p.2 with
      | .function f =>
        if f.params.isEmpty then
          acc.insert p.1 (.function
            { f with
              inputs := f.inputs.map fun (l, t) => (l, rewriteTyp emptySubst mono t),
              output := rewriteTyp emptySubst mono f.output,
              body := rewriteTypedTerm decls emptySubst mono f.body })
        else acc
      | .dataType dt =>
        if dt.params.isEmpty then
          let newCtors := dt.constructors.map fun c =>
            { c with argTypes := c.argTypes.map (rewriteTyp emptySubst mono) }
          acc.insert p.1 (.dataType { dt with constructors := newCtors })
        else acc
      | .constructor dt c =>
        if dt.params.isEmpty then
          let newArgTypes := c.argTypes.map (rewriteTyp emptySubst mono)
          let newCtor : Constructor := { c with argTypes := newArgTypes }
          let rewrittenCtors := dt.constructors.map fun c' =>
            { c' with argTypes := c'.argTypes.map (rewriteTyp emptySubst mono) }
          let newDt : DataType := { dt with constructors := rewrittenCtors }
          acc.insert p.1 (.constructor newDt newCtor)
        else acc
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
  let fnStep : Typed.Decls → Typed.Function → Typed.Decls := fun acc f =>
    acc.insert f.name (.function
      { f with
        inputs := f.inputs.map fun (l, t) => (l, rewriteTyp emptySubst mono t),
        output := rewriteTyp emptySubst mono f.output,
        body := rewriteTypedTerm decls emptySubst mono f.body })
  let fromSource := decls.pairs.toList.foldl srcStep default
  let withNewDts := newDataTypes.toList.foldl dtStep fromSource
  have hconc_eq :
      concretizeBuild decls mono newFunctions newDataTypes =
        newFunctions.toList.foldl fnStep withNewDts := by
    show concretizeBuild decls mono newFunctions newDataTypes =
      newFunctions.toList.foldl fnStep
        (newDataTypes.toList.foldl dtStep
          (decls.pairs.toList.foldl srcStep default))
    unfold concretizeBuild
    repeat rw [← Array.foldl_toList]
    rfl
  rw [hconc_eq] at hget
  have hfn_preserves_other : ∀ (acc : Typed.Decls) (f : Typed.Function) (g' : Global),
      (f.name == g') = false →
      (fnStep acc f).getByKey g' = acc.getByKey g' := by
    intro acc f g' hne
    show (acc.insert f.name _).getByKey g' = acc.getByKey g'
    exact IndexMap.getByKey_insert_of_beq_false _ _ hne
  rcases listFoldl_shape_bwd fnStep Typed.Function.name hfn_preserves_other
    newFunctions.toList withNewDts g with
    hfn_ex | hfn_preserve
  · -- Origin 4: some f ∈ newFunctions has f.name = g.
    obtain ⟨f, hf_mem, hf_eq⟩ := hfn_ex
    exact Or.inr ⟨f, Array.mem_toList_iff.mp hf_mem, hf_eq⟩
  · rw [hfn_preserve] at hget
    -- No fn wrote at g. Examine dtStep fold.
    have hdt_pres_lemma : ∀ (xs : List DataType) (init : Typed.Decls),
          (∀ dt ∈ xs, dt.name ≠ g) →
          (∀ dt ∈ xs, ∀ c ∈ dt.constructors,
            dt.name.pushNamespace c.nameHead ≠ g) →
          (xs.foldl dtStep init).getByKey g = init.getByKey g := by
        intro xs
        induction xs with
        | nil => intros; rfl
        | cons hd tl ih =>
          intro init hno_dt hno_ctor
          simp only [List.foldl_cons]
          have hnd_name : hd.name ≠ g := hno_dt hd List.mem_cons_self
          have hnd_ctor : ∀ c ∈ hd.constructors,
              hd.name.pushNamespace c.nameHead ≠ g :=
            fun c hc => hno_ctor hd List.mem_cons_self c hc
          have ih_tl := ih (dtStep init hd)
            (fun dt hdt => hno_dt dt (List.mem_cons_of_mem _ hdt))
            (fun dt hdt c hc => hno_ctor dt (List.mem_cons_of_mem _ hdt) c hc)
          rw [ih_tl]
          have hnd_beq : (hd.name == g) = false := by
            rw [beq_eq_false_iff_ne]; exact hnd_name
          have h_inner : ∀ (cs : List Constructor) (acc' : Typed.Decls)
              (_hne_cs : ∀ c ∈ cs, hd.name.pushNamespace c.nameHead ≠ g)
              (body : Constructor → Typed.Declaration),
              IndexMap.getByKey (cs.foldl (fun acc'' c =>
                acc''.insert (hd.name.pushNamespace c.nameHead) (body c)) acc') g
              = acc'.getByKey g := by
            intro cs
            induction cs with
            | nil => intros; rfl
            | cons c0 rest ih_cs =>
              intro acc' hne body
              simp only [List.foldl_cons]
              have hnc0 : hd.name.pushNamespace c0.nameHead ≠ g :=
                hne c0 List.mem_cons_self
              have hnc0_beq : (hd.name.pushNamespace c0.nameHead == g) = false := by
                rw [beq_eq_false_iff_ne]; exact hnc0
              have := ih_cs (acc'.insert (hd.name.pushNamespace c0.nameHead) (body c0))
                (fun c' hc' => hne c' (List.mem_cons_of_mem _ hc')) body
              rw [this]
              exact IndexMap.getByKey_insert_of_beq_false _ _ hnc0_beq
          have hnd_ctor_rw : ∀ c ∈ (hd.constructors.map fun c =>
              { c with argTypes := c.argTypes.map (rewriteTyp emptySubst mono) }),
              hd.name.pushNamespace c.nameHead ≠ g := by
            intro c' hc'
            simp only [List.mem_map] at hc'
            obtain ⟨c0, hc0, hc0_eq⟩ := hc'
            rw [← hc0_eq]
            exact hnd_ctor c0 hc0
          rw [h_inner _ _ hnd_ctor_rw _]
          exact IndexMap.getByKey_insert_of_beq_false _ _ hnd_beq
    -- Combined "non-function at g" lemma: if any dt-name=g OR ctor-key=g in xs,
    -- the dtStep foldl yields some `.dataType` or `.constructor` at g (never `.function`).
    have hkey_lemma_nonfn :
        ∀ (xs : List DataType) (init : Typed.Decls),
          (∃ dt ∈ xs, dt.name = g) ∨
          (∃ dt ∈ xs, ∃ c ∈ dt.constructors,
            dt.name.pushNamespace c.nameHead = g) →
          ∃ d, (xs.foldl dtStep init).getByKey g = some d ∧
            (∀ f, d ≠ .function f) := by
      intro xs
      induction xs with
      | nil =>
        intro _ hex
        rcases hex with ⟨_, hm, _⟩ | ⟨_, hm, _⟩ <;> cases hm
      | cons hd tl ih =>
        intro init hex
        simp only [List.foldl_cons]
        by_cases htl_ex : (∃ dt ∈ tl, dt.name = g) ∨
            (∃ dt ∈ tl, ∃ c ∈ dt.constructors,
              dt.name.pushNamespace c.nameHead = g)
        · exact ih _ htl_ex
        · -- The hd is the last writer.
          have htl_no_dt : ∀ dt' ∈ tl, dt'.name ≠ g := by
            intro dt' hdt' heq
            exact htl_ex (Or.inl ⟨dt', hdt', heq⟩)
          have htl_no_ctor : ∀ dt' ∈ tl, ∀ c' ∈ dt'.constructors,
              dt'.name.pushNamespace c'.nameHead ≠ g := by
            intro dt' hdt' c' hc' heq
            exact htl_ex (Or.inr ⟨dt', hdt', c', hc', heq⟩)
          rw [hdt_pres_lemma tl _ htl_no_dt htl_no_ctor]
          -- Now case-split on hex: hd has name g OR hd has a ctor with key g.
          let rewrittenCtors := hd.constructors.map fun c =>
            { c with argTypes := c.argTypes.map (rewriteTyp emptySubst mono) }
          let newDt : DataType := { hd with constructors := rewrittenCtors }
          show ∃ d, IndexMap.getByKey (rewrittenCtors.foldl
              (fun acc'' c =>
                acc''.insert (hd.name.pushNamespace c.nameHead)
                  (.constructor newDt c))
              (init.insert hd.name (.dataType newDt))) g = some d ∧
            (∀ f, d ≠ .function f)
          -- Use a unified "inner ctor fold yields .dataType or .constructor at g"
          -- helper. Either some ctor-key in rewrittenCtors equals g (→ .constructor)
          -- or none does (→ inner fold preserves; outer dt-insert gives .dataType
          -- if hd.name = g; else g comes from earlier).
          by_cases hinner_ex : ∃ c' ∈ rewrittenCtors,
              hd.name.pushNamespace c'.nameHead = g
          · -- Inner ctor-fold writes `.constructor` at g via the last such c'.
            have hctor_fold : ∀ (cs : List Constructor) (acc' : Typed.Decls),
                (∃ c' ∈ cs, hd.name.pushNamespace c'.nameHead = g) →
                ∃ cdt cc, (cs.foldl (fun acc'' c' =>
                  acc''.insert (hd.name.pushNamespace c'.nameHead)
                    (.constructor newDt c')) acc').getByKey g
                  = some (.constructor cdt cc) := by
              intro cs
              induction cs with
              | nil => intro _ ⟨_, hm, _⟩; cases hm
              | cons c0 rest ih_cs =>
                intro acc' hex_cs
                simp only [List.foldl_cons]
                by_cases hrest_ex : ∃ c' ∈ rest,
                    hd.name.pushNamespace c'.nameHead = g
                · exact ih_cs _ hrest_ex
                · obtain ⟨c_last, hc_last_mem, hc_last_eq⟩ := hex_cs
                  have hc_last_is_c0 : c_last = c0 := by
                    rcases List.mem_cons.mp hc_last_mem with rfl | hrest_mem
                    · rfl
                    · exact absurd ⟨c_last, hrest_mem, hc_last_eq⟩ hrest_ex
                  subst hc_last_is_c0
                  have hrest_pres : ∀ (xs : List Constructor) (init' : Typed.Decls),
                      (∀ c' ∈ xs, hd.name.pushNamespace c'.nameHead ≠ g) →
                      IndexMap.getByKey (xs.foldl (fun acc'' c' =>
                        acc''.insert (hd.name.pushNamespace c'.nameHead)
                          (.constructor newDt c')) init') g = init'.getByKey g := by
                    intro xs
                    induction xs with
                    | nil => intros; rfl
                    | cons c1 rest' ih_r =>
                      intro init' hne_all
                      simp only [List.foldl_cons]
                      have hnc1 : hd.name.pushNamespace c1.nameHead ≠ g :=
                        hne_all c1 List.mem_cons_self
                      have hnc1_beq :
                          (hd.name.pushNamespace c1.nameHead == g) = false := by
                        rw [beq_eq_false_iff_ne]; exact hnc1
                      rw [ih_r _ (fun c'' hc'' =>
                        hne_all c'' (List.mem_cons_of_mem _ hc''))]
                      exact IndexMap.getByKey_insert_of_beq_false _ _ hnc1_beq
                  have hrest_ne : ∀ c' ∈ rest,
                      hd.name.pushNamespace c'.nameHead ≠ g := by
                    intro c' hc' heq
                    exact hrest_ex ⟨c', hc', heq⟩
                  rw [hrest_pres rest _ hrest_ne]
                  refine ⟨newDt, c_last, ?_⟩
                  rw [← hc_last_eq]
                  exact IndexMap.getByKey_insert_self _ _ _
            obtain ⟨cdt_v, cc_v, hfinal⟩ := hctor_fold _ _ hinner_ex
            exact ⟨_, hfinal, fun _ h => by cases h⟩
          · -- No ctor-key collision in hd; inner fold preserves init.insert hd.name.
            have hno_inner_g : ∀ c ∈ rewrittenCtors,
                hd.name.pushNamespace c.nameHead ≠ g := by
              intro c hc heq
              exact hinner_ex ⟨c, hc, heq⟩
            have h_inner_pres : ∀ (cs : List Constructor) (acc' : Typed.Decls)
                (_hne : ∀ c ∈ cs, hd.name.pushNamespace c.nameHead ≠ g),
                IndexMap.getByKey (cs.foldl (fun acc'' c =>
                  acc''.insert (hd.name.pushNamespace c.nameHead)
                    (.constructor newDt c)) acc') g
                = acc'.getByKey g := by
              intro cs
              induction cs with
              | nil => intros; rfl
              | cons c0 rest ih_cs =>
                intro acc' hne
                simp only [List.foldl_cons]
                have hnc0 : hd.name.pushNamespace c0.nameHead ≠ g :=
                  hne c0 List.mem_cons_self
                have hnc0_beq : (hd.name.pushNamespace c0.nameHead == g) = false := by
                  rw [beq_eq_false_iff_ne]; exact hnc0
                rw [ih_cs _ (fun c'' hc'' => hne c'' (List.mem_cons_of_mem _ hc''))]
                exact IndexMap.getByKey_insert_of_beq_false _ _ hnc0_beq
            rw [h_inner_pres _ _ hno_inner_g]
            -- Now hd.name must equal g (else hex would not have a writer).
            -- Because hex is satisfied but no inner-ctor-fold writes,
            -- hex's ctor-disjunct must use hd's ctor — but hno_inner_g forbids that
            -- via the rewriteCtors map (each c ∈ hd.constructors maps to a c' with
            -- the same nameHead). So hex's ctor disjunct on hd is also impossible.
            -- Therefore hex's dt disjunct holds: hd.name = g.
            have hhd_eq : hd.name = g := by
              rcases hex with ⟨dt_ex, hdt_ex_mem, hdt_ex_eq⟩ | ⟨dt_ex, hdt_ex_mem, c_ex, hc_ex_mem, hc_ex_eq⟩
              · -- dt-name disjunct
                have : dt_ex = hd := by
                  rcases List.mem_cons.mp hdt_ex_mem with rfl | htl_mem
                  · rfl
                  · exact absurd hdt_ex_eq (htl_no_dt dt_ex htl_mem)
                rw [← this]; exact hdt_ex_eq
              · -- ctor-key disjunct: must be in hd (else htl_no_ctor contradicts)
                exfalso
                have hdt_is_hd : dt_ex = hd := by
                  rcases List.mem_cons.mp hdt_ex_mem with rfl | htl_mem
                  · rfl
                  · exact absurd hc_ex_eq (htl_no_ctor dt_ex htl_mem c_ex hc_ex_mem)
                subst hdt_is_hd
                -- c_ex's rewritten variant has the same nameHead.
                let c_ex_rw : Constructor :=
                  { c_ex with argTypes := c_ex.argTypes.map (rewriteTyp emptySubst mono) }
                have h_rw_mem : c_ex_rw ∈ rewrittenCtors := by
                  rw [List.mem_map]
                  exact ⟨c_ex, hc_ex_mem, rfl⟩
                exact hno_inner_g _ h_rw_mem hc_ex_eq
            refine ⟨.dataType newDt, ?_, fun _ h => by cases h⟩
            rw [← hhd_eq]
            exact IndexMap.getByKey_insert_self _ _ _
    -- Outer split: dt-name OR ctor-key vs neither.
    by_cases hdt_or_ctor_ex :
        (∃ dt ∈ newDataTypes.toList, dt.name = g) ∨
        (∃ dt ∈ newDataTypes.toList, ∃ c ∈ dt.constructors,
          dt.name.pushNamespace c.nameHead = g)
    · -- Some `.dataType`/`.constructor` writer at g → contradicts `.function` hget.
      exfalso
      obtain ⟨d, hd_eq, hd_nfn⟩ :=
        hkey_lemma_nonfn newDataTypes.toList fromSource hdt_or_ctor_ex
      rw [hd_eq] at hget
      simp only [Option.some.injEq] at hget
      exact hd_nfn _ hget
    · -- Neither dt.name=g nor ctor-key=g in newDataTypes. dtStep fold preserves.
      have hno_dt_name : ∀ dt ∈ newDataTypes.toList, dt.name ≠ g := by
        intro dt hdt heq
        exact hdt_or_ctor_ex (Or.inl ⟨dt, hdt, heq⟩)
      have hno_ctor : ∀ dt ∈ newDataTypes.toList, ∀ c ∈ dt.constructors,
          dt.name.pushNamespace c.nameHead ≠ g := by
        intro dt hdt c hc heq
        exact hdt_or_ctor_ex (Or.inr ⟨dt, hdt, c, hc, heq⟩)
      rw [hdt_pres_lemma newDataTypes.toList fromSource hno_dt_name hno_ctor] at hget
      show (∃ f_src, decls.getByKey g = some (.function f_src) ∧ f_src.params = []) ∨ _
      -- Trace srcStep fold: any srcStep arm gives `.function`/`.dataType`/`.constructor`.
      -- Origin 1 is the fn-arm with f.params = [].
      have hsrc_shape : ∀ (pairs : List (Global × Typed.Declaration))
          (init : Typed.Decls),
          (∀ p ∈ pairs, decls.getByKey p.1 = some p.2) →
          (pairs.foldl srcStep init).getByKey g = some (.function f_mono) →
          (∃ f_src, decls.getByKey g = some (.function f_src)
            ∧ f_src.params = []) ∨
          init.getByKey g = some (.function f_mono) := by
        intro pairs
        induction pairs with
        | nil =>
          intro init _ hfold
          right; exact hfold
        | cons hd tl ih =>
          intro init hpairs hfold
          simp only [List.foldl_cons] at hfold
          have hpairs_tl : ∀ p ∈ tl, decls.getByKey p.1 = some p.2 :=
            fun p hp => hpairs p (List.mem_cons_of_mem _ hp)
          have hpairs_hd : decls.getByKey hd.1 = some hd.2 := hpairs hd List.mem_cons_self
          rcases ih (srcStep init hd) hpairs_tl hfold with hleft | hmid
          · exact Or.inl hleft
          · obtain ⟨k, dd⟩ := hd
            simp only at hmid hpairs_hd
            cases dd with
            | function f =>
              by_cases hp : f.params.isEmpty = true
              · simp only [srcStep, hp, if_true] at hmid
                by_cases hk : (k == g) = true
                · have hkeq : k = g := LawfulBEq.eq_of_beq hk
                  refine Or.inl ⟨f, ?_, ?_⟩
                  · rw [← hkeq]; exact hpairs_hd
                  · cases hfp : f.params with
                    | nil => rfl
                    | cons _ _ => rw [hfp] at hp; cases hp
                · have hk' : (k == g) = false := Bool.not_eq_true _ |>.mp hk
                  rw [IndexMap.getByKey_insert_of_beq_false _ _ hk'] at hmid
                  exact Or.inr hmid
              · simp only [srcStep, hp, if_false, Bool.false_eq_true] at hmid
                exact Or.inr hmid
            | dataType dt =>
              by_cases hp : dt.params.isEmpty = true
              · simp only [srcStep, hp, if_true] at hmid
                by_cases hk : (k == g) = true
                · have hkeq : k = g := LawfulBEq.eq_of_beq hk
                  rw [hkeq] at hmid
                  rw [IndexMap.getByKey_insert_self] at hmid
                  cases hmid
                · have hk' : (k == g) = false := Bool.not_eq_true _ |>.mp hk
                  rw [IndexMap.getByKey_insert_of_beq_false _ _ hk'] at hmid
                  exact Or.inr hmid
              · simp only [srcStep, hp, if_false, Bool.false_eq_true] at hmid
                exact Or.inr hmid
            | constructor dt c =>
              by_cases hp : dt.params.isEmpty = true
              · simp only [srcStep, hp, if_true] at hmid
                by_cases hk : (k == g) = true
                · have hkeq : k = g := LawfulBEq.eq_of_beq hk
                  rw [hkeq] at hmid
                  rw [IndexMap.getByKey_insert_self] at hmid
                  cases hmid
                · have hk' : (k == g) = false := Bool.not_eq_true _ |>.mp hk
                  rw [IndexMap.getByKey_insert_of_beq_false _ _ hk'] at hmid
                  exact Or.inr hmid
              · simp only [srcStep, hp, if_false, Bool.false_eq_true] at hmid
                exact Or.inr hmid
      have hdefault_none : (default : Typed.Decls).getByKey g = none := by
        unfold IndexMap.getByKey
        show ((default : Typed.Decls).indices[g]?).bind _ = none
        have : (default : Typed.Decls).indices[g]? = none := by
          show ((default : Std.HashMap Global Nat))[g]? = none
          exact Std.HashMap.getElem?_empty
        rw [this]; rfl
      have hpairs_hyp : ∀ p ∈ decls.pairs.toList, decls.getByKey p.1 = some p.2 := by
        intro p hp
        rcases p with ⟨a, b⟩
        exact IndexMap.getByKey_of_mem_pairs _ _ _ hp
      rcases hsrc_shape decls.pairs.toList default hpairs_hyp hget with hleft | hmid
      · exact Or.inl hleft
      · rw [hdefault_none] at hmid
        cases hmid

/-! #### Main theorem. -/

/-- Every `.dataType` key in `cd` comes from a source `.dataType` at some
`templateName` via `concretizeName templateName args = g`. -/
theorem templateOf_exists
    {tds : Typed.Decls} {cd : Concrete.Decls}
    (hconc : tds.concretize = .ok cd)
    (_hunique : Typed.Decls.ConcretizeUniqueNames tds)
    {g : Global} {cdt : Concrete.DataType}
    (hget : cd.getByKey g = some (.dataType cdt)) :
    ∃ (templateName : Global) (templateDt : DataType),
      TemplateOf tds cd g templateName templateDt := by
  -- Unfold `concretize` to get drained + monoDecls = concretizeBuild ...
  have hconc_copy := hconc
  unfold Typed.Decls.concretize at hconc_copy
  simp only [bind, Except.bind] at hconc_copy
  split at hconc_copy
  · contradiction
  rename_i drained hdrain
  let monoDecls : Typed.Decls :=
    concretizeBuild tds drained.mono drained.newFunctions drained.newDataTypes
  have hmono_def : monoDecls =
      concretizeBuild tds drained.mono drained.newFunctions drained.newDataTypes := rfl
  have hfold : monoDecls.foldlM (init := default) step4Lower = .ok cd := hconc_copy
  have hcd_contains : cd.containsKey g := by
    rw [← IndexMap.getByKey_ne_none_iff_containsKey]
    rw [hget]; exact Option.some_ne_none _
  have hkeys := concretize_step_4_keys_of_fold step4Lower step4Lower_inserts hfold
  have hmono_contains : monoDecls.containsKey g := (hkeys g).mpr hcd_contains
  obtain ⟨d_mono, hget_mono⟩ : ∃ d, monoDecls.getByKey g = some d := by
    have := (IndexMap.getByKey_ne_none_iff_containsKey monoDecls g).mpr hmono_contains
    rcases h : monoDecls.getByKey g with _ | d
    · exact absurd h this
    · exact ⟨d, rfl⟩
  have hshape := step4Lower_fold_kind_at_key hget_mono hfold
  have hd_mono_is_dt : ∃ dt_mono, d_mono = .dataType dt_mono := by
    cases d_mono with
    | function f =>
      exfalso
      simp only at hshape
      obtain ⟨cf, hcf⟩ := hshape
      rw [hcf] at hget
      cases hget
    | dataType dt => exact ⟨dt, rfl⟩
    | constructor dt c =>
      exfalso
      simp only at hshape
      obtain ⟨cdt', cc, hcc⟩ := hshape
      rw [hcc] at hget
      cases hget
  obtain ⟨dt_mono, hd_mono_eq⟩ := hd_mono_is_dt
  subst hd_mono_eq
  rw [hmono_def] at hget_mono
  have hdrain_inv : drained.StrongNewNameShape tds := by
    have hinit : DrainState.StrongNewNameShape tds _ :=
      DrainState.StrongNewNameShape.init tds (concretizeSeed tds)
    exact concretize_drain_preserves_StrongNewNameShape _ _ hinit hdrain
  have hshape_origin := concretizeBuild_dataType_origin tds drained.mono
    drained.newFunctions drained.newDataTypes hget_mono
  rcases hshape_origin with ⟨dt_src, hsrc, _hparams⟩ | ⟨dt, hdtmem, hdt_eq_g⟩
  · exact ⟨g, dt_src, hsrc, ⟨cdt, hget⟩, ⟨#[], concretizeName_empty_args g⟩⟩
  · have hshape_dt := hdrain_inv.2 dt hdtmem
    obtain ⟨gSrc, args, dt_orig, hname, hget_src, _hargs_sz, _hctors⟩ := hshape_dt
    have hname_eq_g : concretizeName gSrc args = g := by rw [← hname, hdt_eq_g]
    exact ⟨gSrc, dt_orig, hget_src, ⟨cdt, hget⟩, args, hname_eq_g⟩

theorem templateOf_unique
    {tds : Typed.Decls} {cd : Concrete.Decls}
    (hconc : tds.concretize = .ok cd)
    (hunique : Typed.Decls.ConcretizeUniqueNames tds)
    {g : Global}
    {templateName₁ templateName₂ : Global}
    {templateDt₁ templateDt₂ : DataType}
    (h₁ : TemplateOf tds cd g templateName₁ templateDt₁)
    (h₂ : TemplateOf tds cd g templateName₂ templateDt₂) :
    templateName₁ = templateName₂ := by
  obtain ⟨_ht₁, ⟨cdt₁, hget₁⟩, args₁, hname₁⟩ := h₁
  obtain ⟨_ht₂, _hcdt₂, args₂, hname₂⟩ := h₂
  have hnames : concretizeName templateName₁ args₁
      = concretizeName templateName₂ args₂ := by rw [hname₁, hname₂]
  have hexists : ∃ d, cd.getByKey (concretizeName templateName₁ args₁) = some d := by
    refine ⟨.dataType cdt₁, ?_⟩
    rw [hname₁]; exact hget₁
  exact (hunique hconc templateName₁ templateName₂ args₁ args₂ hnames hexists).1

open scoped Classical in
noncomputable def templateOf
    (tds : Typed.Decls) (cd : Concrete.Decls)
    (hconc : tds.concretize = .ok cd)
    (hunique : Typed.Decls.ConcretizeUniqueNames tds) (g : Global) : Global :=
  if h : ∃ cdt, cd.getByKey g = some (.dataType cdt) then
    (templateOf_exists hconc hunique h.choose_spec).choose
  else
    g

theorem templateOf_spec
    {tds : Typed.Decls} {cd : Concrete.Decls}
    (hconc : tds.concretize = .ok cd)
    (hunique : Typed.Decls.ConcretizeUniqueNames tds)
    {g : Global} {cdt : Concrete.DataType}
    (hget : cd.getByKey g = some (.dataType cdt)) :
    ∃ templateDt : DataType,
      TemplateOf tds cd g (templateOf tds cd hconc hunique g) templateDt := by
  have hex : ∃ cdt', cd.getByKey g = some (.dataType cdt') := ⟨cdt, hget⟩
  have hunfold : templateOf tds cd hconc hunique g =
      (templateOf_exists hconc hunique hex.choose_spec).choose := by
    unfold templateOf
    simp [hex]
  obtain ⟨templateDt, htemplate⟩ :=
    (templateOf_exists hconc hunique hex.choose_spec).choose_spec
  refine ⟨templateDt, ?_⟩
  rw [hunfold]; exact htemplate

private theorem templateOf_eq_witness
    {tds : Typed.Decls} {cd : Concrete.Decls}
    (hconc : tds.concretize = .ok cd)
    (hunique : Typed.Decls.ConcretizeUniqueNames tds)
    {g : Global} {templateName : Global} {templateDt : DataType}
    (h : TemplateOf tds cd g templateName templateDt) :
    templateOf tds cd hconc hunique g = templateName := by
  obtain ⟨_htds, ⟨cdt, hget⟩, _hargs⟩ := h
  obtain ⟨_templateDt', htemplate'⟩ := templateOf_spec hconc hunique hget
  have horig : TemplateOf tds cd g templateName templateDt :=
    ⟨_htds, ⟨cdt, hget⟩, _hargs⟩
  exact templateOf_unique hconc hunique htemplate' horig

-- `RankTransport` def moved to `Ix/Aiur/Semantics/ConcreteInvariants.lean`.

/-- **Main theorem**: given tds-side rank witness + `RankTransport`, every
cd-dt ctor argtype has bounded cd-side spine.

**Proof outline**:
1. Backward-trace `cdt.constructors` through `step4Lower` to `dt_mono.constructors`
   in `monoDecls`.
2. Backward-trace `dt_mono` through `concretizeBuild` to `templateDt` (the
   source template): either `dt_mono` came from a monomorphic source
   (`fromSource` fold, args = `#[]`) or from `drained.newDataTypes`
   (`withNewDts` fold, where each entry has ctors =
   `templateDt.constructors.map (.argTypes.map (Typ.instantiate subst))`).
3. Each cd-ctor argtype `t` is `typToConcrete emptyMono (rewriteTyp emptySubst
   mono t_rewritten)` where `t_rewritten` is the instantiated source argtype.
4. Structural induction on `t` dispatches: `.unit`/`.field`/`.pointer`/`.function`
   are immediate; `.tuple`/`.array` recurse; `.ref g'` requires the rank lift
   via `RankTransport`.

**BLOCKED status (F=1)**: two pieces of infrastructure are missing:

(a) **Backward trace from cd-ctor-argtypes to source ctor-argtypes**:
    ~500 LoC across 3 phases (`fromSource`, `withNewDts`, `newFunctions`) of
    `concretizeBuild`, each preserving a pre-image invariant on ctor argTypes.
    Structurally parallel to `L2_phase1_fromSource` /
    `L2_phase2_withNewDts` / `L2_phase3_newFunctions` (which track dt-shape
    at a key) but adapted to track the exact ctor-argtype-to-source-argtype
    correspondence.

(b) **`templateOf_of_source_ref` lemma**: if `.ref g'` survives from a
    source tds ctor-argtype to a cd-ctor-argtype (i.e., g' is not rewritten
    away by instantiate + rewriteTyp + typToConcrete) AND
    `cd.getByKey g' = some (.dataType _)`, then
    `templateOf tds cd hconc hunique g' = g'`. Required for the `.ref g'`
    case to reduce `rank_cd g' < rank_cd g` to the source-side
    `rank_src g' < rank_src templateName`.
    Proof sketch: under `hunique` + `concretizeName_empty_args g' = g'`,
    any template `(templateName', args')` with
    `concretizeName templateName' args' = g'` and `cd.getByKey g' = dt` must
    have `templateName' = g'` and `args' = #[]` — because source `.ref g'`
    points to a source dt-key g' (by type-wellformedness; under FullyMono
    this dt is monomorphic so survives at key g'), and uniqueness rules out
    any other template producing g'.
    Subtle: requires a `FullyMono`-style hypothesis or drain-level invariant
    not currently threaded here.

Downstream caller `concretize_preserves_direct_dag` depends on this; it
feeds into `sizeBound_ok_of_rank` which certifies `Decls.SizeBoundOk cd`. -/
theorem spine_transfer
    {tds : Typed.Decls} {cd : Concrete.Decls}
    (_hconc : tds.concretize = .ok cd)
    (_hunique : Typed.Decls.ConcretizeUniqueNames tds)
    {rank_src : Global → Nat}
    (_hrank_src : ∀ g dt, tds.getByKey g = some (.dataType dt) →
        ∀ c ∈ dt.constructors, ∀ t ∈ c.argTypes,
          Typed.Typ.SpineRefsBelow rank_src (rank_src g) t ∧
          Typed.Typ.ParamSafe dt.params t)
    {rank_cd : Global → Nat}
    (_htransport : RankTransport tds cd rank_src rank_cd)
    {g : Global} {cdt : Concrete.DataType}
    (_hget : cd.getByKey g = some (.dataType cdt))
    {templateName : Global} {templateDt : DataType}
    (_htemplate : TemplateOf tds cd g templateName templateDt) :
    ∀ c ∈ cdt.constructors, ∀ t ∈ c.argTypes,
      Concrete.Typ.SpineRefsBelow rank_cd (rank_cd g) t := by
  -- BLOCKED: See docstring above. Closing requires the backward-trace +
  -- rank-lift infrastructure (~500-700 LoC of `concretizeBuild` per-phase
  -- per-ctor-argtype preservation, paralleling existing `L2_phase1_fromSource`
  -- / `L2_phase2_withNewDts` / `L2_phase3_newFunctions` + a new
  -- `templateOf_of_source_ref` lemma).
  sorry

end DirectDagBody

private theorem concretize_preserves_direct_dag
    {tds : Typed.Decls} {cd : Concrete.Decls}
    (hconc : tds.concretize = .ok cd)
    (hacyclic : Typed.Decls.NoDirectDatatypeCycles tds)
    (hunique : Typed.Decls.ConcretizeUniqueNames tds) :
    ∃ rank : Global → Nat,
      ∀ g dt, cd.getByKey g = some (.dataType dt) →
        ∀ c ∈ dt.constructors, ∀ t ∈ c.argTypes,
          Concrete.Typ.SpineRefsBelow rank (rank g) t := by
  obtain ⟨rank_src, hrank_src⟩ := hacyclic
  let origin : Global → Global := DirectDagBody.templateOf tds cd hconc hunique
  let rank_cd : Global → Nat := fun g => rank_src (origin g)
  refine ⟨rank_cd, ?_⟩
  have htransport : DirectDagBody.RankTransport tds cd rank_src rank_cd := by
    intro g templateName templateDt htemplate
    show rank_src (origin g) = rank_src templateName
    have heq : origin g = templateName :=
      DirectDagBody.templateOf_eq_witness hconc hunique htemplate
    rw [heq]
  intro g cdt hget c hc t ht
  obtain ⟨templateDt, htemplate⟩ := DirectDagBody.templateOf_spec hconc hunique hget
  exact DirectDagBody.spine_transfer hconc hunique hrank_src htransport hget htemplate c hc t ht

-- `SizeBoundVisInv` DELETED (orphan — mentioned only in `sizeBound_ok_of_rank`'s
-- FINDINGS comment as a proof strategy hint, never consumed). Reintroduce if
-- `sizeBound_ok_of_rank`'s proof actually needs it.

/-- Structural invariant: every `.dataType` in `cd` is keyed by its own name.
True of `concretize`'s output (see `Compiler/Concretize.lean:889, 920`), but
not part of `Concrete.Decls`'s type — must be proved as a separate theorem
about concretize output. -/
@[expose]
def Concrete.Decls.DtNameIsKey (cd : Concrete.Decls) : Prop :=
  ∀ g dt, cd.getByKey g = some (.dataType dt) → g = dt.name

/- `concretize_produces_dtNameIsKey` moved to `CompilerProgress.lean` (takes
a `Typed.Decls.DtNameIsKey` hypothesis discharged by
`checkAndSimplify_preserves_dtNameIsKey`). -/

/-! ### Typ.sizeBound under SpineRefsBelow + vis invariant.

The core lemma for `sizeBound_ok_of_rank`: given a spine-bounded rank witness
and an invariant on `vis` ("every `g'' ∈ vis` has `rank g'' ≥ bd`"), every
`DataType.sizeBound` / `Typ.sizeBound` recursion succeeds. -/

/-- Vis invariant carried through `sizeBound_ok_strong`: every element of
`vis` that IS a cd-dt key has rank strictly greater than `rank g`. Elements of
`vis` that are NOT cd-dt keys are unconstrained (the visited check only
triggers for cd-dt keys in practice). -/
@[expose]
def SizeBoundVisInv (cd : Concrete.Decls) (rank : Global → Nat) (g : Global)
    (vis : Std.HashSet Global) : Prop :=
  ∀ g'' : Global, vis.contains g'' = true →
    ∀ dt'', cd.getByKey g'' = some (.dataType dt'') → rank g'' > rank g

/-- Strong-induction core lemma: given SpineRefsBelow-form rank + DtNameIsKey +
RefClosed, `DataType.sizeBound` succeeds at every `(bound, vis)` whose cd-dt
members have rank strictly greater than `rank g`. Recursion grows `vis` by
`dt.name = g` while dropping current rank to `rank g' < rank g`; the invariant
is preserved pointwise because new `vis` elements are either old (with rank
> old-rank > new-rank) or `g` (with rank = old-rank > new-rank). -/
private theorem sizeBound_ok_strong
    (cd : Concrete.Decls)
    (hrc : Concrete.Decls.RefClosed cd)
    (hdtkey : Concrete.Decls.DtNameIsKey cd)
    (rank : Global → Nat)
    (hrank : ∀ g dt, cd.getByKey g = some (.dataType dt) →
        ∀ c ∈ dt.constructors, ∀ t ∈ c.argTypes,
          Concrete.Typ.SpineRefsBelow rank (rank g) t) :
    ∀ (n : Nat) (g : Global) (dt : Concrete.DataType)
      (bound : Nat) (vis : Std.HashSet Global),
      rank g = n →
      cd.getByKey g = some (.dataType dt) →
      SizeBoundVisInv cd rank g vis →
      ∃ m, Concrete.DataType.sizeBound cd bound vis dt = .ok m := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro g dt bound vis hrankEq hget hvis
    cases bound with
    | zero =>
      refine ⟨1, ?_⟩; unfold Concrete.DataType.sizeBound; rfl
    | succ bound' =>
      -- `¬ vis.contains dt.name`: dt.name = g (DtNameIsKey); if g ∈ vis, the
      -- vis invariant gives `rank g > rank g` via cd.getByKey g = .dataType dt.
      have hdtName : g = dt.name := hdtkey g dt hget
      have hnvis : ¬ vis.contains dt.name = true := by
        intro hc
        rw [← hdtName] at hc
        have : rank g > rank g := hvis g hc dt hget
        exact Nat.lt_irrefl _ this
      unfold Concrete.DataType.sizeBound
      simp only [hnvis, if_false, Bool.false_eq_true]
      simp only [bind, Except.bind, pure, Except.pure]
      -- Typ-level helper: spine-bounded rank → Typ.sizeBound succeeds.
      -- Invariant on `v`: every cd-dt key in v has rank strictly greater than rank g.
      have htypBound : ∀ (b : Nat) (t : Concrete.Typ) (v : Std.HashSet Global),
          Concrete.Typ.RefClosed cd t →
          Concrete.Typ.SpineRefsBelow rank (rank g) t →
          (∀ g'' : Global, v.contains g'' = true →
              ∀ dt'', cd.getByKey g'' = some (.dataType dt'') →
                rank g'' ≥ rank g) →
          ∃ k, Concrete.Typ.sizeBound cd b v t = .ok k := by
        intro b
        induction b with
        | zero =>
          intros; refine ⟨0, ?_⟩; unfold Concrete.Typ.sizeBound; rfl
        | succ b' ihb =>
          intro t v hrc_t hspine hv_inv
          cases t with
          | unit =>
            refine ⟨0, ?_⟩; unfold Concrete.Typ.sizeBound; rfl
          | field =>
            refine ⟨1, ?_⟩; unfold Concrete.Typ.sizeBound; rfl
          | pointer t' =>
            refine ⟨1, ?_⟩; unfold Concrete.Typ.sizeBound; rfl
          | function ins out =>
            refine ⟨1, ?_⟩; unfold Concrete.Typ.sizeBound; rfl
          | tuple ts =>
            cases hrc_t; rename_i hrc_ts
            cases hspine; rename_i hsp_ts
            unfold Concrete.Typ.sizeBound
            conv in Array.foldlM _ _ _ => rw [← Array.foldlM_toList]
            simp only [Array.toList_attach, List.attachWith]
            apply List.foldlM_except_ok'
            intro acc t' ht'
            obtain ⟨t'val, ht'mem, ht'eq⟩ := List.mem_pmap.mp ht'
            subst ht'eq
            obtain ⟨m, hm⟩ := ihb t'val v (hrc_ts t'val ht'mem) (hsp_ts t'val ht'mem) hv_inv
            exact ⟨acc + m, by simp [hm, bind, Except.bind, pure, Except.pure]⟩
          | array t' n₁ =>
            cases hrc_t; rename_i hrc_inner
            cases hspine; rename_i hsp_inner
            obtain ⟨m, hm⟩ := ihb t' v hrc_inner hsp_inner hv_inv
            refine ⟨n₁ * m, ?_⟩
            unfold Concrete.Typ.sizeBound
            simp only [hm, bind, Except.bind, pure, Except.pure]
          | ref g'' =>
            cases hrc_t; rename_i hdt'
            obtain ⟨dt', hget'⟩ := hdt'
            cases hspine; rename_i hrank_lt
            -- rank g'' < rank g. Recurse via outer IH at rank g''.
            have hrank_lt_n : rank g'' < n := hrankEq ▸ hrank_lt
            have hvis' : SizeBoundVisInv cd rank g'' v := by
              intro g''' hc dt''' hget'''
              have := hv_inv g''' hc dt''' hget'''  -- rank g''' ≥ rank g
              exact Nat.lt_of_lt_of_le hrank_lt this
            obtain ⟨k, hk⟩ := ih (rank g'') hrank_lt_n g'' dt' b' v rfl hget' hvis'
            refine ⟨k, ?_⟩
            unfold Concrete.Typ.sizeBound
            simp only [hget', hk]
      -- Vis invariant after inserting dt.name = g: every cd-dt key g'' in
      -- (vis.insert dt.name) has rank g'' ≥ rank g.
      have hVisInsert :
          ∀ g'' : Global, (vis.insert dt.name).contains g'' = true →
            ∀ dt'', cd.getByKey g'' = some (.dataType dt'') → rank g'' ≥ rank g := by
        intro g'' hc dt'' hget''
        rw [Std.HashSet.contains_insert] at hc
        rcases Bool.or_eq_true .. |>.mp hc with heq | hin
        · have hname : dt.name = g'' := LawfulBEq.eq_of_beq heq
          rw [← hname, ← hdtName]
          exact Nat.le_refl _
        · exact Nat.le_of_lt (hvis g'' hin dt'' hget'')
      -- mapM over dt.constructors.
      have hMap := @List.mapM_except_ok _ _ _
        (Concrete.Constructor.sizeBound cd bound' (vis.insert dt.name))
        dt.constructors (by
          intro c hc
          unfold Concrete.Constructor.sizeBound
          apply List.foldlM_except_ok'
          intro acc t ht
          have hrc_decl : Concrete.Declaration.RefClosed cd (.dataType dt) :=
            hrc g _ hget
          have hrc_t : Concrete.Typ.RefClosed cd t := hrc_decl c hc t ht
          have hspine : Concrete.Typ.SpineRefsBelow rank (rank g) t :=
            hrank g dt hget c hc t ht
          obtain ⟨k, hk⟩ :=
            htypBound bound' t (vis.insert dt.name) hrc_t hspine hVisInsert
          exact ⟨acc + k, by simp [hk, bind, Except.bind, pure, Except.pure]⟩)
      obtain ⟨sizes, hsizes⟩ := hMap
      refine ⟨sizes.foldl max 0 + 1, ?_⟩
      simp [hsizes, bind, Except.bind, pure, Except.pure]

/-- Size-bound termination from a spine-bounded rank witness + DtNameIsKey.
The entry-point `SizeBoundOk cd` form quantifies over `vis` with full
cd-dt disjointness; that disjointness vacuously satisfies
`SizeBoundVisInv` (no cd-dt keys in vis → the rank-greater hypothesis
is vacuous). -/
private theorem sizeBound_ok_of_rank
    (cd : Concrete.Decls)
    (hrc : Concrete.Decls.RefClosed cd)
    (hdtkey : Concrete.Decls.DtNameIsKey cd)
    (rank : Global → Nat)
    (hrank : ∀ g dt, cd.getByKey g = some (.dataType dt) →
        ∀ c ∈ dt.constructors, ∀ t ∈ c.argTypes,
          Concrete.Typ.SpineRefsBelow rank (rank g) t) :
    Concrete.Decls.SizeBoundOk cd := by
  intro bound vis dt hex hdisjoint
  obtain ⟨g, hget⟩ := hex
  -- hdisjoint: for all g' dt', cd.getByKey g' = .dataType dt' → ¬ vis.contains dt'.name.
  -- Translate to SizeBoundVisInv: any g'' ∈ vis that IS a cd-dt key contradicts
  -- disjointness (since DtNameIsKey gives dt''.name = g'', and g'' ∈ vis).
  have hVisInv : SizeBoundVisInv cd rank g vis := by
    intro g'' hcontains dt'' hget''
    exfalso
    have hname : g'' = dt''.name := hdtkey g'' dt'' hget''
    have : ¬ vis.contains dt''.name = true := hdisjoint g'' dt'' hget''
    rw [← hname] at this
    exact this hcontains
  exact sizeBound_ok_strong cd hrc hdtkey rank hrank (rank g) g dt bound vis rfl hget hVisInv

/-- `concretize` output has no direct datatype cycles (`SizeBoundOk`).
Composed from `concretize_produces_refClosed` + `concretize_preserves_direct_dag`
+ `concretize_produces_dtNameIsKey` + `sizeBound_ok_of_rank`.

Takes `hDtNameIsKey_tds` and `hCtorPresent_tds` to thread into
`concretize_produces_refClosed` (downstream discharge, `CompilerProgress`). -/
theorem concretize_produces_sizeBoundOk
    {t : Source.Toplevel} {tds : Typed.Decls} {cd : Concrete.Decls}
    (hmono : FullyMonomorphic t)
    (hts : t.checkAndSimplify = .ok tds)
    (hconc : tds.concretize = .ok cd)
    (hacyclic : Typed.Decls.NoDirectDatatypeCycles tds)
    (hunique : Typed.Decls.ConcretizeUniqueNames tds)
    (hdtkey : Concrete.Decls.DtNameIsKey cd)
    (hDtNameIsKey_tds : ∀ (key : Global) (dt : DataType),
      (key, Typed.Declaration.dataType dt) ∈ tds.pairs.toList → key = dt.name)
    (hCtorPresent_tds : ∀ (dtkey : Global) (dt : DataType) (c : Constructor),
      (dtkey, Typed.Declaration.dataType dt) ∈ tds.pairs.toList →
      c ∈ dt.constructors →
      ∃ cc, (dt.name.pushNamespace c.nameHead,
        Typed.Declaration.constructor dt cc) ∈ tds.pairs.toList) :
    Concrete.Decls.SizeBoundOk cd := by
  have hrc := concretize_produces_refClosed hmono hts hconc hunique
    hDtNameIsKey_tds hCtorPresent_tds
  obtain ⟨rank, hrank⟩ := concretize_preserves_direct_dag hconc hacyclic hunique
  exact sizeBound_ok_of_rank cd hrc hdtkey rank hrank

/-- Concretize's layout map succeeds on every concretize-output `cd`. Requires
the source-level acyclicity hypothesis + `DtNameIsKey cd` (discharged upstream
by `concretize_produces_dtNameIsKey` + source-level `DtNameIsKey tds`). Threads
`hDtNameIsKey_tds` / `hCtorPresent_tds` through to `concretize_produces_refClosed`. -/
theorem concretize_layoutMap_progress
    {t : Source.Toplevel} {tds : Typed.Decls} {cd : Concrete.Decls}
    (hmono : FullyMonomorphic t)
    (hts : t.checkAndSimplify = .ok tds)
    (hconc : tds.concretize = .ok cd)
    (hacyclic : Typed.Decls.NoDirectDatatypeCycles tds)
    (hunique : Typed.Decls.ConcretizeUniqueNames tds)
    (hdtkey : Concrete.Decls.DtNameIsKey cd)
    (hDtNameIsKey_tds : ∀ (key : Global) (dt : DataType),
      (key, Typed.Declaration.dataType dt) ∈ tds.pairs.toList → key = dt.name)
    (hCtorPresent_tds : ∀ (dtkey : Global) (dt : DataType) (c : Constructor),
      (dtkey, Typed.Declaration.dataType dt) ∈ tds.pairs.toList →
      c ∈ dt.constructors →
      ∃ cc, (dt.name.pushNamespace c.nameHead,
        Typed.Declaration.constructor dt cc) ∈ tds.pairs.toList) :
    ∃ lm, Concrete.Decls.layoutMap cd = .ok lm :=
  layoutMap_ok_of_refClosed cd
    (concretize_produces_refClosed hmono hts hconc hunique hDtNameIsKey_tds hCtorPresent_tds)
    (concretize_produces_sizeBoundOk hmono hts hconc hacyclic hunique hdtkey
      hDtNameIsKey_tds hCtorPresent_tds)

-- `Typed.Decls.concretize_progress` DELETED (orphan wrapper over the deleted
-- `concretize_ok_of_invariants`). `Toplevel.compile_progress` uses
-- `WellFormed.monoTerminates` directly.

-- `typFlatSize_eq_typSize_of_concretize` DELETED (orphan speculative infra —
-- no caller). Reintroduce with proper sig when a specific caller needs the
-- source/concrete flat-size equality.

/-- Layout-insertion keys match source keys. Under `IndexMap`'s
`pairsIndexed` (source keys are distinct), this ensures no layout-insert
overwrites another. Decomposes into `NameAgrees` + `DtNameIsKey` + `CtorIsKey`
plus a `CtorPresent`-style side (every ctor-insert key is already a `.constructor`
entry in `cd`, hence distinct from any `.dataType` key by IndexMap uniqueness). -/
@[expose]
def Concrete.Decls.LayoutKeysMatch (cd : Concrete.Decls) : Prop :=
  (∀ g f, cd.getByKey g = some (.function f) → g = f.name) ∧
  (∀ g dt, cd.getByKey g = some (.dataType dt) → g = dt.name) ∧
  (∀ g dt c, cd.getByKey g = some (.constructor dt c) →
    g = dt.name.pushNamespace c.nameHead) ∧
  (∀ g dt, cd.getByKey g = some (.dataType dt) →
    ∀ c ∈ dt.constructors, ∃ cdt cc,
      cd.getByKey (dt.name.pushNamespace c.nameHead) = some (.constructor cdt cc))


/-- IndexMap keys are unique: two `.toList` elements with equal first
components are the same element. -/
private theorem IndexMap.pairs_toList_keys_unique
    {α β : Type} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] [LawfulBEq α]
    (m : IndexMap α β) (p1 p2 : α × β)
    (h1 : p1 ∈ m.pairs.toList) (h2 : p2 ∈ m.pairs.toList)
    (hkey : p1.1 = p2.1) : p1 = p2 := by
  obtain ⟨i1, hi1, heq1⟩ := List.getElem_of_mem h1
  obtain ⟨i2, hi2, heq2⟩ := List.getElem_of_mem h2
  rw [Array.length_toList] at hi1 hi2
  have hg1 : m.pairs[i1]'hi1 = p1 := by rw [← heq1, Array.getElem_toList]
  have hg2 : m.pairs[i2]'hi2 = p2 := by rw [← heq2, Array.getElem_toList]
  have hp1i : m.indices[p1.1]? = some i1 := by
    have := m.pairsIndexed i1 hi1; rw [hg1] at this; exact this
  have hp2i : m.indices[p2.1]? = some i2 := by
    have := m.pairsIndexed i2 hi2; rw [hg2] at this; exact this
  rw [hkey] at hp1i
  have hii : i1 = i2 := Option.some.inj (hp1i.symm.trans hp2i)
  subst hii; rw [← hg1, ← hg2]

/-- Helper: given `cd.layoutMap = .ok lm`, every `.dataType dt` pair in `cd`
has `lm[dt.name]? = some (.dataType _)`.

**Proof structure**:
1. Unfold `cd.layoutMap` to the fold form over `cd.pairs.toList`.
2. Bridge `hget : cd.getByKey g = some (.dataType dt)` to
   `(g, .dataType dt) ∈ cd.pairs.toList` via `pairsIndexed` + `LawfulBEq`.
3. Induct on the fold suffix with invariant "for every `(g', .dataType dt')`
   in the processed prefix, `acc.1[dt'.name]? = some (.dataType _)`".
4. Step preservation uses 4 distinctness facts assembled inline:
   - `hFnDtName`: a function-insert at `f.name = gF` can't overwrite a prior
     dataType's `dt'.name = gD` entry (IndexMap-uniqueness contradiction).
   - `hDtDtName`: two `.dataType` entries with equal `.name` coincide.
   - `hDtCtorKey`: a prior `.dataType` at `g'` can't be overwritten by a
     constructor-insert at `dt_h.name.pushNamespace c.nameHead` — because
     `hLKM.2.2.2` (ctorPresent) proves an actual `.constructor` entry at
     that key in cd, so a rival `.dataType` at that key contradicts IndexMap
     uniqueness.
   - For the current-step dataType (head case): `Global.ne_pushNamespace` —
     no ctor-insert key equals the inserted dt's own name. -/
theorem layoutMap_getByKey_dt
    {cd : Concrete.Decls} {lm : LayoutMap}
    (hlm : cd.layoutMap = .ok lm)
    (hLKM : Concrete.Decls.LayoutKeysMatch cd)
    {g : Global} {dt : Concrete.DataType}
    (hget : cd.getByKey g = some (.dataType dt)) :
    ∃ n, lm[dt.name]? = some (.dataType n) := by
  -- Unfold layoutMap to fold form.
  have hrw : Concrete.Decls.layoutMap cd = (do
      let r ← cd.pairs.toList.foldlM (layoutMapPass cd)
        (({}, 0) : LayoutMap × Nat)
      pure r.1) := by
    unfold Concrete.Decls.layoutMap
    simp only [IndexMap.foldlM]
    rw [← Array.foldlM_toList]
    rfl
  rw [hrw] at hlm
  -- Extract the inner fold result.
  cases hfold_r : cd.pairs.toList.foldlM (layoutMapPass cd)
                    (({}, 0) : LayoutMap × Nat) with
  | error e => rw [hfold_r] at hlm; simp [bind, Except.bind] at hlm
  | ok res =>
    rw [hfold_r] at hlm
    simp only [bind, Except.bind, pure, Except.pure] at hlm
    -- hlm : res.1 = lm; we prove ∃ n, res.1[dt.name]? = some (.dataType n).
    -- Bridge hget → membership in pairs.toList.
    have hmem : (g, Concrete.Declaration.dataType dt) ∈ cd.pairs.toList := by
      unfold IndexMap.getByKey at hget
      cases hi : cd.indices[g]? with
      | none => rw [hi] at hget; simp at hget
      | some i =>
        rw [hi] at hget
        have hbindform : (some i >>= (cd.pairs[·]?.map Prod.snd))
            = cd.pairs[i]?.map Prod.snd := rfl
        rw [hbindform] at hget
        have hlt : i < cd.pairs.size := (cd.validIndices g hi).1
        have hget? : cd.pairs[i]? = some (cd.pairs[i]'hlt) := by
          rw [Array.getElem?_eq_some_iff]; exact ⟨hlt, rfl⟩
        rw [hget?] at hget
        simp only [Option.map_some] at hget
        have hfstBeq : (cd.pairs[i]'hlt).1 == g := (cd.validIndices g hi).2
        have hfstEq : (cd.pairs[i]'hlt).1 = g := LawfulBEq.eq_of_beq hfstBeq
        rw [Array.mem_toList_iff, Array.mem_iff_getElem]
        refine ⟨i, hlt, ?_⟩
        cases hp : cd.pairs[i]'hlt with
        | mk a b =>
          rw [hp] at hfstEq hget
          -- hfstEq : a = g, hget : some (a, b).snd = some (.dataType dt)
          simp only [Option.some.injEq] at hget
          -- hget : (a, b).snd = .dataType dt, i.e. b = .dataType dt
          show (a, b) = (g, Concrete.Declaration.dataType dt)
          subst hfstEq
          exact Prod.mk.injEq _ _ _ _ |>.mpr ⟨rfl, hget⟩
    -- Abbreviate cd.pairs.toList as L.
    let L : List (Global × Concrete.Declaration) := cd.pairs.toList
    have hL : L = cd.pairs.toList := rfl
    -- Key fact (for key-uniqueness in L): two pairs with equal first component coincide.
    have hUniqL : ∀ (p1 p2 : Global × Concrete.Declaration),
        p1 ∈ L → p2 ∈ L → p1.1 = p2.1 → p1 = p2 := fun p1 p2 h1 h2 hk =>
      IndexMap.pairs_toList_keys_unique cd p1 p2
        (by rw [hL] at h1; exact h1) (by rw [hL] at h2; exact h2) hk
    -- Dtn=ctor-key distinctness lemma (uses hLKM's ctorPresent conjunct).
    -- If cd has `.dataType dt''` at g'' and `.dataType dt'` at g' (in L), with
    -- `c ∈ dt'.constructors`, then `g'' ≠ dt'.name.pushNamespace c.nameHead`.
    have hDtCtorKey :
      ∀ (g'' g' : Global) (dt'' dt' : Concrete.DataType) (c : Concrete.Constructor),
        (g'', Concrete.Declaration.dataType dt'') ∈ L →
        (g', Concrete.Declaration.dataType dt') ∈ L →
        c ∈ dt'.constructors →
        g'' ≠ dt'.name.pushNamespace c.nameHead := by
      intro g'' g' dt'' dt' c h1 h2 hc
      have hg'eq : cd.getByKey g' = some (.dataType dt') :=
        IndexMap.getByKey_of_mem_pairs _ _ _ h2
      -- Derive ctor-presence in cd.
      obtain ⟨cdt, cc, hctorGet⟩ := hLKM.2.2.2 g' dt' hg'eq c hc
      have hg''eq : cd.getByKey g'' = some (.dataType dt'') :=
        IndexMap.getByKey_of_mem_pairs _ _ _ h1
      intro hkey
      -- Then cd.getByKey g'' = .constructor cdt cc (from hctorGet, rewriting by hkey).
      rw [hkey] at hg''eq
      rw [hctorGet] at hg''eq
      cases hg''eq
    -- Dt-dt name distinctness: two .dataType entries with same dt.name have same pair.
    have hDtDtName :
      ∀ (g₁ g₂ : Global) (dt₁ dt₂ : Concrete.DataType),
        (g₁, Concrete.Declaration.dataType dt₁) ∈ L →
        (g₂, Concrete.Declaration.dataType dt₂) ∈ L →
        dt₁.name = dt₂.name → g₁ = g₂ ∧ dt₁ = dt₂ := by
      intro g₁ g₂ dt₁ dt₂ h1 h2 hname
      have hg1 : cd.getByKey g₁ = some (.dataType dt₁) :=
        IndexMap.getByKey_of_mem_pairs _ _ _ h1
      have hg2 : cd.getByKey g₂ = some (.dataType dt₂) :=
        IndexMap.getByKey_of_mem_pairs _ _ _ h2
      have hk1 : g₁ = dt₁.name := hLKM.2.1 g₁ dt₁ hg1
      have hk2 : g₂ = dt₂.name := hLKM.2.1 g₂ dt₂ hg2
      have hk : g₁ = g₂ := by rw [hk1, hk2, hname]
      have hpair : (g₁, Concrete.Declaration.dataType dt₁) =
                   (g₂, Concrete.Declaration.dataType dt₂) :=
        hUniqL _ _ h1 h2 hk
      refine ⟨hk, ?_⟩
      have h2nd : Concrete.Declaration.dataType dt₁ = Concrete.Declaration.dataType dt₂ :=
        (Prod.mk.injEq _ _ _ _).mp hpair |>.2
      cases h2nd; rfl
    -- Fn-dt name distinctness: function-entry key ≠ any dataType's dt.name.
    have hFnDtName :
      ∀ (gF gD : Global) (f : Concrete.Function) (dtD : Concrete.DataType),
        (gF, Concrete.Declaration.function f) ∈ L →
        (gD, Concrete.Declaration.dataType dtD) ∈ L →
        f.name ≠ dtD.name := by
      intro gF gD f dtD hF hD heq
      have hgF : cd.getByKey gF = some (.function f) :=
        IndexMap.getByKey_of_mem_pairs _ _ _ hF
      have hgD : cd.getByKey gD = some (.dataType dtD) :=
        IndexMap.getByKey_of_mem_pairs _ _ _ hD
      have hkF : gF = f.name := hLKM.1 gF f hgF
      have hkD : gD = dtD.name := hLKM.2.1 gD dtD hgD
      have hkFD : gF = gD := by rw [hkF, hkD, heq]
      -- Two pairs at same key with different decls → contradiction.
      have hp := hUniqL _ _ hF hD hkFD
      injection hp with _ hdecl
      cases hdecl
    -- Main fold induction. Target: ∃ n, res.1[dt.name]? = some (.dataType n).
    -- We prove: for any suffix `ys` of L, if fold from init succeeds to `acc`,
    -- and init already satisfies "every seen dt pair has its dt.name entry
    -- populated", and invariant is preserved, then final acc satisfies it on
    -- all pairs in (prefix ++ ys) = L.
    -- Formalize with explicit prefix/suffix decomposition.
    suffices h : ∀ (prefixL ys : List (Global × Concrete.Declaration))
        (init final : LayoutMap × Nat),
      prefixL ++ ys = L →
      (∀ g' dt', (g', Concrete.Declaration.dataType dt') ∈ prefixL →
          ∃ n, init.1[dt'.name]? = some (.dataType n)) →
      ys.foldlM (layoutMapPass cd) init = .ok final →
      ∀ g' dt', (g', Concrete.Declaration.dataType dt') ∈ prefixL ++ ys →
          ∃ n, final.1[dt'.name]? = some (.dataType n) by
      have hall := h [] L ({}, 0) res rfl (by simp) hfold_r
      rw [List.nil_append] at hall
      have hfinal := hall g dt hmem
      -- hlm : Except.ok res.fst = Except.ok lm ⇒ res.fst = lm.
      have hres_eq : res.1 = lm := by
        injection hlm
      rw [hres_eq] at hfinal
      exact hfinal
    intro prefixL ys
    induction ys generalizing prefixL with
    | nil =>
      intro init final _hprefEq hinit hfold
      simp only [List.foldlM_nil, pure, Except.pure] at hfold
      cases hfold
      intro g' dt' hmem'
      rw [List.append_nil] at hmem'
      exact hinit g' dt' hmem'
    | cons head rest ih =>
      intro init final hprefEq hinit hfold
      simp only [List.foldlM_cons, bind, Except.bind] at hfold
      split at hfold
      · cases hfold
      · rename_i acc' hstep
        -- Apply IH with prefix := prefixL ++ [head], ys := rest, init := acc'.
        have hprefEq' : (prefixL ++ [head]) ++ rest = L := by
          rw [List.append_assoc]; exact hprefEq
        intro g' dt' hmemFinal
        -- head ∈ L.
        have hhead_memL : head ∈ L := by
          rw [← hprefEq]
          exact List.mem_append_right _ (List.mem_cons_self)
        -- Key: acc' preserves dataType entries for prefixL pairs + adds head if it's a dataType.
        have hinit' : ∀ g'' dt'',
            (g'', Concrete.Declaration.dataType dt'') ∈ prefixL ++ [head] →
            ∃ n, acc'.1[dt''.name]? = some (.dataType n) := by
          intro g' dt' hmem'
          rw [List.mem_append] at hmem'
          rcases hmem' with hin_pref | hin_head
          · -- In prefixL: preserved by step (we show acc'.1[dt'.name]? = init.1[dt'.name]?).
            obtain ⟨n, hn⟩ := hinit g' dt' hin_pref
            -- Show: step preserves dt'.name lookup when (g', dataType dt') was in prefixL.
            -- For that, need: head's insertion keys ≠ dt'.name.
            -- head.snd is .dataType / .function / .constructor. Case-split.
            -- First, membership of (g', .dataType dt') in L (via prefixL ⊆ L).
            have hmemL : (g', Concrete.Declaration.dataType dt') ∈ L := by
              rw [← hprefEq]; exact List.mem_append_left _ hin_pref
            -- Unfold step on head.
            obtain ⟨headKey, headDecl⟩ := head
            unfold layoutMapPass at hstep
            cases headDecl with
            | constructor _ _ =>
              simp only at hstep
              -- No insert; acc' = init.
              have : acc' = (init.1, init.2) := by
                simp [pure, Except.pure] at hstep
                exact hstep.symm
              rw [this]
              exact ⟨n, hn⟩
            | function f =>
              -- step computes inputSize, outputSize, offsets; inserts at f.name.
              -- Extract the insert: acc'.1 = init.1.insert f.name (.function _).
              simp only [bind, Except.bind] at hstep
              split at hstep
              · cases hstep
              · rename_i _ _
                split at hstep
                · cases hstep
                · split at hstep
                  · cases hstep
                  · -- After three binds, hstep : pure ... = .ok acc'
                    simp only [pure, Except.pure, Except.ok.injEq] at hstep
                    -- hstep : (init.1.insert f.name (.function ...), init.2 + 1) = acc'
                    -- Show acc'.1[dt'.name]? = some (.dataType n).
                    -- Need f.name ≠ dt'.name.
                    have hne : f.name ≠ dt'.name :=
                      hFnDtName headKey g' f dt' hhead_memL hmemL
                    refine ⟨n, ?_⟩
                    rw [← hstep]
                    show (init.1.insert f.name _)[dt'.name]? = some (.dataType n)
                    rw [Std.HashMap.getElem?_insert]
                    have hbeq : (f.name == dt'.name) = false := by simp [hne]
                    simp only [hbeq, Bool.false_eq_true, ↓reduceIte]
                    exact hn
            | dataType dt_h =>
              -- step: inserts at dt_h.name (.dataType size), then ctor fold inserts at
              -- dt_h.name.pushNamespace c.nameHead for each c ∈ dt_h.constructors.
              simp only [bind, Except.bind] at hstep
              split at hstep
              · cases hstep
              · rename_i dataTypeSize hdtSize
                -- Inner ctor fold.
                split at hstep
                · cases hstep
                · rename_i innerRes hinnerFold
                  simp only [pure, Except.pure, Except.ok.injEq] at hstep
                  -- hstep : (innerRes.1, init.2) = acc'
                  -- Need: acc'.1[dt'.name]? = some (.dataType n).
                  -- acc'.1 = innerRes.1; innerRes derived from inner fold starting at
                  -- (init.1.insert dt_h.name (.dataType dataTypeSize), 0).
                  -- First show: (init.1.insert dt_h.name (.dataType dataTypeSize))[dt'.name]?
                  -- = some (.dataType n) if dt_h.name ≠ dt'.name,
                  -- or = some (.dataType dataTypeSize) if dt_h.name = dt'.name.
                  -- Either way, it's some (.dataType _).
                  -- Then need ctor fold to preserve that (ctor inserts at
                  -- dt_h.name.pushNamespace c.nameHead ≠ dt'.name).
                  -- headKey for .dataType: by hLKM.2.1, headKey = dt_h.name.
                  have hHeadGet : cd.getByKey headKey = some (.dataType dt_h) :=
                    IndexMap.getByKey_of_mem_pairs _ _ _ hhead_memL
                  have hHeadKeyEq : headKey = dt_h.name := hLKM.2.1 headKey dt_h hHeadGet
                  -- Sub-claim: (init.1.insert dt_h.name (.dataType dataTypeSize))[dt'.name]?
                  --         = some (.dataType _)
                  have hAfterDtInsert :
                      ∃ m, (init.1.insert dt_h.name (.dataType dataTypeSize))[dt'.name]?
                            = some (.dataType m) := by
                    by_cases hn_eq : dt_h.name = dt'.name
                    · refine ⟨dataTypeSize, ?_⟩
                      rw [Std.HashMap.getElem?_insert]
                      simp [hn_eq]
                    · refine ⟨n, ?_⟩
                      rw [Std.HashMap.getElem?_insert]
                      have hbeq : (dt_h.name == dt'.name) = false := by simp [hn_eq]
                      simp only [hbeq, Bool.false_eq_true, ↓reduceIte]
                      exact hn
                  -- Now the ctor fold. For each c ∈ dt_h.constructors, it inserts at
                  -- dt_h.name.pushNamespace c.nameHead. By hDtCtorKey:
                  --   g' ≠ dt_h.name.pushNamespace c.nameHead
                  -- (since (g', .dataType dt') ∈ L, (headKey = dt_h.name, .dataType dt_h) ∈ L).
                  -- Thus ctor inserts don't overwrite dt'.name entry.
                  -- Preservation lemma: list-style invariance.
                  obtain ⟨m, hmInit⟩ := hAfterDtInsert
                  refine ⟨m, ?_⟩
                  rw [← hstep]
                  show innerRes.1[dt'.name]? = some (.dataType m)
                  have hDt'Key : g' = dt'.name := hLKM.2.1 g' dt'
                    (IndexMap.getByKey_of_mem_pairs _ _ _ hmemL)
                  -- g' ≠ dt_h.name.pushNamespace c.nameHead for each c ∈ dt_h.constructors.
                  have hNoOverwrite : ∀ c ∈ dt_h.constructors,
                      dt'.name ≠ dt_h.name.pushNamespace c.nameHead := by
                    intro c hc
                    have := hDtCtorKey g' headKey dt' dt_h c hmemL hhead_memL hc
                    rw [hDt'Key] at this
                    exact this
                  -- Prove: starting from any state whose dt'.name entry is some .dataType _,
                  -- the ctor fold preserves that.
                  have hStrong :
                    ∀ (cs : List Concrete.Constructor) (s0 sf : LayoutMap × Nat),
                      (∀ c ∈ cs, c ∈ dt_h.constructors) →
                      s0.1[dt'.name]? = some (Layout.dataType m) →
                      List.foldlM
                        (fun (state : LayoutMap × Nat)
                             (constructor : Concrete.Constructor) => do
                          let offsets ← constructor.argTypes.foldlM
                              (init := (#[0] : Array Nat))
                              (fun (offsets : Array Nat) (typ : Concrete.Typ) => do
                                let typSyze ← typ.size cd
                                pure $ offsets.push
                                  ((offsets[offsets.size - 1]?.getD 0) + typSyze))
                          let decl : Layout :=
                            Layout.constructor
                              { size := dataTypeSize, offsets := offsets,
                                index := state.2 : ConstructorLayout }
                          let name := dt_h.name.pushNamespace constructor.nameHead
                          pure (state.1.insert name decl, state.2 + 1))
                        s0 cs = .ok sf →
                      sf.1[dt'.name]? = some (Layout.dataType m) := by
                    intro cs
                    induction cs with
                    | nil =>
                      intro s0 sf _ hstart hfold0
                      simp only [List.foldlM_nil, pure, Except.pure,
                        Except.ok.injEq] at hfold0
                      subst hfold0; exact hstart
                    | cons c rest ihCs =>
                      intro s0 sf hcMemAll hstart hfold0
                      simp only [List.foldlM_cons, bind, Except.bind] at hfold0
                      -- hfold0 has a nested inner bind for offsets. Split on that.
                      split at hfold0
                      · cases hfold0
                      · rename_i stateAfterC hstateEq
                        -- hstateEq : (let v ← offsets_fold; pure (s0.insert ..., s0.snd+1))
                        --            = .ok stateAfterC
                        -- hfold0 : rest.foldlM ... stateAfterC = .ok sf
                        -- stateAfterC : LayoutMap × Nat is the state after processing c.
                        -- Apply IH to rest from stateAfterC, assuming stateAfterC[dt'.name]? is OK.
                        have hcMem : c ∈ dt_h.constructors :=
                          hcMemAll c List.mem_cons_self
                        have hne : dt'.name ≠ dt_h.name.pushNamespace c.nameHead :=
                          hNoOverwrite c hcMem
                        -- From hstateEq: split on the offsets fold.
                        have hsDt : stateAfterC.1[dt'.name]? = some (Layout.dataType m) := by
                          split at hstateEq
                          · cases hstateEq
                          · rename_i offsArr _hoffs
                            -- hstateEq : pure (s0.insert ..., s0.snd+1) = .ok stateAfterC
                            simp only [pure, Except.pure, Except.ok.injEq] at hstateEq
                            rw [← hstateEq]
                            change (s0.1.insert (dt_h.name.pushNamespace c.nameHead)
                                (Layout.constructor
                                  { size := dataTypeSize, offsets := offsArr,
                                    index := s0.2 }))[dt'.name]?
                              = some (Layout.dataType m)
                            rw [Std.HashMap.getElem?_insert]
                            have hbeq : (dt_h.name.pushNamespace c.nameHead == dt'.name)
                                = false := by simp [Ne.symm hne]
                            simp only [hbeq, Bool.false_eq_true, ↓reduceIte]
                            exact hstart
                        exact ihCs _ sf
                          (fun c' hc' => hcMemAll c' (List.mem_cons_of_mem _ hc'))
                          hsDt hfold0
                  -- Apply hStrong with s0 := (init.1.insert dt_h.name (.dataType dataTypeSize), 0).
                  exact hStrong dt_h.constructors _ innerRes
                    (fun _ hc => hc) hmInit hinnerFold
          · -- hin_head : head ∈ [head] → head itself.
            simp only [List.mem_singleton] at hin_head
            -- head = (g', .dataType dt'). So headKey = g', headDecl = .dataType dt'.
            -- Step inserts at dt'.name.
            subst hin_head
            -- Now step is on (g', .dataType dt'). Unfold it.
            unfold layoutMapPass at hstep
            simp only [bind, Except.bind] at hstep
            split at hstep
            · cases hstep
            · rename_i dataTypeSize _hdtSize
              split at hstep
              · cases hstep
              · rename_i innerRes hinnerFold
                simp only [pure, Except.pure, Except.ok.injEq] at hstep
                refine ⟨dataTypeSize, ?_⟩
                rw [← hstep]
                show innerRes.1[dt'.name]? = some (Layout.dataType dataTypeSize)
                -- Inner ctor fold from (init.1.insert dt'.name (.dataType dataTypeSize), 0)
                -- preserves dt'.name entry (ctor inserts at dt'.name.pushNamespace ≠ dt'.name).
                have hNoOv : ∀ c ∈ dt'.constructors,
                    dt'.name ≠ dt'.name.pushNamespace c.nameHead :=
                  fun _ _ => Global.ne_pushNamespace _ _
                have hStrong :
                  ∀ (cs : List Concrete.Constructor) (s0 sf : LayoutMap × Nat),
                    (∀ c ∈ cs, c ∈ dt'.constructors) →
                    s0.1[dt'.name]? = some (Layout.dataType dataTypeSize) →
                    List.foldlM
                      (fun (state : LayoutMap × Nat)
                           (constructor : Concrete.Constructor) => do
                        let offsets ← constructor.argTypes.foldlM
                            (init := (#[0] : Array Nat))
                            (fun (offsets : Array Nat) (typ : Concrete.Typ) => do
                              let typSyze ← typ.size cd
                              pure $ offsets.push
                                ((offsets[offsets.size - 1]?.getD 0) + typSyze))
                        let decl : Layout :=
                          Layout.constructor
                            { size := dataTypeSize, offsets := offsets,
                              index := state.2 : ConstructorLayout }
                        let name := dt'.name.pushNamespace constructor.nameHead
                        pure (state.1.insert name decl, state.2 + 1))
                      s0 cs = .ok sf →
                    sf.1[dt'.name]? = some (Layout.dataType dataTypeSize) := by
                  intro cs
                  induction cs with
                  | nil =>
                    intro s0 sf _ hstart hfold0
                    simp only [List.foldlM_nil, pure, Except.pure,
                      Except.ok.injEq] at hfold0
                    subst hfold0; exact hstart
                  | cons c rest ihCs =>
                    intro s0 sf hcMemAll hstart hfold0
                    simp only [List.foldlM_cons, bind, Except.bind] at hfold0
                    split at hfold0
                    · cases hfold0
                    · rename_i stateAfterC hstateEq
                      have hcMem : c ∈ dt'.constructors :=
                        hcMemAll c List.mem_cons_self
                      have hne : dt'.name ≠ dt'.name.pushNamespace c.nameHead :=
                        hNoOv c hcMem
                      have hsDt : stateAfterC.1[dt'.name]?
                          = some (Layout.dataType dataTypeSize) := by
                        split at hstateEq
                        · cases hstateEq
                        · rename_i offsArr _hoffs
                          simp only [pure, Except.pure, Except.ok.injEq] at hstateEq
                          rw [← hstateEq]
                          change (s0.1.insert (dt'.name.pushNamespace c.nameHead)
                              (Layout.constructor
                                { size := dataTypeSize, offsets := offsArr,
                                  index := s0.2 }))[dt'.name]?
                            = some (Layout.dataType dataTypeSize)
                          rw [Std.HashMap.getElem?_insert]
                          have hbeq : (dt'.name.pushNamespace c.nameHead == dt'.name)
                              = false := by simp [Ne.symm hne]
                          simp only [hbeq, Bool.false_eq_true, ↓reduceIte]
                          exact hstart
                      exact ihCs _ sf
                        (fun c' hc' => hcMemAll c' (List.mem_cons_of_mem _ hc'))
                        hsDt hfold0
                exact hStrong dt'.constructors _ innerRes
                  (fun _ hc => hc)
                  Std.HashMap.getElem?_insert_self
                  hinnerFold
        refine ih _ _ _ hprefEq' hinit' hfold g' dt' ?_
        -- Goal: (g', .dataType dt') ∈ (prefixL ++ [head]) ++ rest
        -- Have: hmemFinal : (g', .dataType dt') ∈ prefixL ++ (head :: rest)
        -- These are syntactically different; convert.
        rw [List.append_assoc, List.singleton_append]
        exact hmemFinal

/-- `typSize lm t` succeeds on every `RefClosed` concrete type under a
sound `layoutMap`. `layoutMap`-level variant of `typSize_ok_of_refClosed`. -/
theorem typSize_ok_of_refClosed_lm
    {cd : Concrete.Decls} {lm : LayoutMap}
    (hlm : cd.layoutMap = .ok lm)
    (hdtkey : Concrete.Decls.DtNameIsKey cd)
    (hLKM : Concrete.Decls.LayoutKeysMatch cd)
    {t : Concrete.Typ}
    (hrc : Concrete.Typ.RefClosed cd t) :
    ∃ n, typSize lm t = .ok n := by
  induction hrc with
  | unit => refine ⟨0, ?_⟩; unfold typSize; rfl
  | field => refine ⟨1, ?_⟩; unfold typSize; rfl
  | pointer _ _ => refine ⟨1, ?_⟩; unfold typSize; rfl
  | function => refine ⟨1, ?_⟩; unfold typSize; rfl
  | @tuple ts hts ih =>
    unfold typSize
    conv in Array.foldlM _ _ _ => rw [← Array.foldlM_toList]
    apply List.foldlM_except_ok'
    intro acc t' ht'
    obtain ⟨m, hm⟩ := ih t' ht'
    exact ⟨acc + m, by simp [hm, bind, Except.bind, pure, Except.pure]⟩
  | @array inner n hinner ih =>
    obtain ⟨m, hm⟩ := ih
    refine ⟨n * m, ?_⟩
    unfold typSize
    simp only [hm, bind, Except.bind, pure, Except.pure]
  | @ref g hdt =>
    obtain ⟨dt, hgetG⟩ := hdt
    have hgeq : g = dt.name := hdtkey g dt hgetG
    obtain ⟨n, hn⟩ := layoutMap_getByKey_dt hlm hLKM hgetG
    refine ⟨n, ?_⟩
    unfold typSize
    rw [hgeq, hn]
    rfl


/-- `concretize` lifts a typed-function entry to a concrete-function entry at
`concName = name` (monomorphic), preserving input flat-size identity.

**Sig strengthened (2026-04-24, SORRY_AUDIT_AGENT2.md)**: the prior
`_htf_mono : tf.params.isEmpty = true` was too weak — flat-size identity can
fail when other polymorphic datatypes are reachable from `tf.inputs` (e.g.
`.app list [.field]` resolves to a specialized dt with different ctor-argtype
content). Replaced with `FullyMonomorphic t` + `t.mkDecls = .ok decls` +
`t.checkAndSimplify = .ok typedDecls` so ALL source decls are monomorphic
and `.app` rewrites are vacuous. Caller discharge via `hwf.fullyMonomorphic`. -/
theorem concretize_extract_function_at_name
    {t : Source.Toplevel} {decls : Source.Decls}
    {typedDecls : Typed.Decls} {concDecls : Concrete.Decls}
    (_hmono : FullyMonomorphic t)
    (_hdecls : t.mkDecls = .ok decls)
    (_hts : t.checkAndSimplify = .ok typedDecls)
    (_hconc : typedDecls.concretize = .ok concDecls)
    {name : Global} {tf : Typed.Function}
    (_htyped : typedDecls.getByKey name = some (.function tf)) :
    ∃ (concName : Global) (concF : Concrete.Function),
      concName = name ∧
      concDecls.getByKey concName = some (.function concF) ∧
      ∀ (layoutMap : LayoutMap), concDecls.layoutMap = .ok layoutMap →
        (tf.inputs.map Prod.snd).foldl
            (fun acc t => acc + typFlatSize decls {} t) 0 =
          (concF.inputs.map Prod.snd).foldl
            (fun acc t => acc + (typSize layoutMap t).toOption.getD 0) 0 := by
  sorry


end Aiur

end
