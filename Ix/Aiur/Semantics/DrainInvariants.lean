module
public import Ix.Aiur.Compiler.Concretize

/-!
Invariants on `DrainState` — the pure-fold state threaded through `concretize`'s
Step 2 worklist (`concretizeDrain` / `concretizeDrainEntry` / `concretizeDrainIter`).

These pair every `(g, args) ↦ g'` entry in the mono-map with a corresponding
pushed decl: `MonoHasDecl` says the named decl exists; `MonoShapeOk` says its
constructor shape is exactly the instantiation of the source template by `args`.

Both are preserved by `concretizeDrainEntry` (the `.function`/`.dataType` arms
push-and-insert in lock-step) and hence by the full drain. Both hold vacuously
for the empty initial state constructed by `Typed.Decls.concretize`.

Used to repair the signatures of `Proofs/ConcretizeSound.lean`
(`concretize_drain_mono_has_decl` / `concretize_drain_shape_equation`), which
were false as originally stated (arbitrary `init` with no invariant admits
counterexamples under `fuel = 0` + empty pending).
-/

public section
@[expose] section

namespace Aiur

open Source

/-- Invariant on a `DrainState`: every `(g, args) ↦ g'` in `st.mono` has a
corresponding pushed decl in `st.newFunctions` or `st.newDataTypes` named
`g'`. Preserved by `concretizeDrainEntry`: the `.function`/`.dataType` arms
of that step both push-and-insert in lock-step. -/
def DrainState.MonoHasDecl (st : DrainState) : Prop :=
  ∀ (g : Global) (args : Array Typ) (g' : Global),
    st.mono[(g, args)]? = some g' →
    (∃ f ∈ st.newFunctions, f.name = g') ∨
    (∃ dt ∈ st.newDataTypes, dt.name = g')

/-- The initial state used by `Typed.Decls.concretize` satisfies `MonoHasDecl`
vacuously (empty mono + empty arrays). -/
theorem DrainState.MonoHasDecl.init (pending : Std.HashSet (Global × Array Typ)) :
    DrainState.MonoHasDecl
      { pending, seen := {}, mono := {}, newFunctions := #[], newDataTypes := #[] } := by
  intro g args g' hmono
  rw [Std.HashMap.getElem?_empty] at hmono
  cases hmono

/-- Invariant on a `DrainState`: for every `(g, args) ↦ g'` in `st.mono` where
`decls.getByKey g = some (.dataType dt)`, `st.newDataTypes` contains a
datatype named `g'` whose constructors are `dt.constructors` pointwise
instantiated via `mkParamSubst dt.params args`. Preserved by
`concretizeDrainEntry`: the `.dataType` arm builds exactly this shape when
inserting. Paired with `MonoHasDecl` in the `MonoShapeOk` proof. -/
def DrainState.MonoShapeOk (decls : Typed.Decls) (st : DrainState) : Prop :=
  ∀ (g : Global) (args : Array Typ) (g' : Global),
    st.mono[(g, args)]? = some g' →
    ∀ {dt : DataType},
      decls.getByKey g = some (.dataType dt) →
      ∃ newDt ∈ st.newDataTypes,
        newDt.name = g' ∧
        newDt.constructors = dt.constructors.map fun c =>
          { c with argTypes := c.argTypes.map (Typ.instantiate (mkParamSubst dt.params args)) }

/-- The initial state used by `Typed.Decls.concretize` satisfies `MonoShapeOk`
vacuously. -/
theorem DrainState.MonoShapeOk.init (decls : Typed.Decls)
    (pending : Std.HashSet (Global × Array Typ)) :
    DrainState.MonoShapeOk decls
      { pending, seen := {}, mono := {}, newFunctions := #[], newDataTypes := #[] } := by
  intro g args g' hmono _ _
  rw [Std.HashMap.getElem?_empty] at hmono
  cases hmono

/-- Drain invariant: every pushed `newFunctions`/`newDataTypes` entry's name is
`concretizeName g args` for some `(g, args)` whose source origin is the
matching declaration kind in `decls`. -/
def DrainState.NewNameShape (decls : Typed.Decls) (st : DrainState) : Prop :=
  (∀ f ∈ st.newFunctions,
    ∃ (g : Global) (args : Array Typ) (f_orig : Typed.Function),
      f.name = concretizeName g args ∧
      decls.getByKey g = some (.function f_orig)) ∧
  (∀ dt ∈ st.newDataTypes,
    ∃ (g : Global) (args : Array Typ) (dt_orig : DataType),
      dt.name = concretizeName g args ∧
      decls.getByKey g = some (.dataType dt_orig))

/-- Empty initial state satisfies `NewNameShape` vacuously. -/
theorem DrainState.NewNameShape.init (decls : Typed.Decls)
    (pending : Std.HashSet (Global × Array Typ)) :
    DrainState.NewNameShape decls
      { pending, seen := {}, mono := {}, newFunctions := #[], newDataTypes := #[] } := by
  refine ⟨?_, ?_⟩
  · intro f hf
    simp only [Array.not_mem_empty] at hf
  · intro dt hdt
    simp only [Array.not_mem_empty] at hdt

/-- Strengthened drain invariant: every pushed `newFunctions`/`newDataTypes`
entry additionally carries its args size (= source template params length)
and, for datatypes, the constructor `nameHead`-map correspondence. -/
def DrainState.StrongNewNameShape (decls : Typed.Decls) (st : DrainState) : Prop :=
  (∀ f ∈ st.newFunctions,
    ∃ (g : Global) (args : Array Typ) (f_orig : Typed.Function),
      f.name = concretizeName g args ∧
      decls.getByKey g = some (.function f_orig) ∧
      args.size = f_orig.params.length) ∧
  (∀ dt ∈ st.newDataTypes,
    ∃ (g : Global) (args : Array Typ) (dt_orig : DataType),
      dt.name = concretizeName g args ∧
      decls.getByKey g = some (.dataType dt_orig) ∧
      args.size = dt_orig.params.length ∧
      dt.constructors.map (·.nameHead) = dt_orig.constructors.map (·.nameHead))

/-- Empty initial state satisfies `StrongNewNameShape` vacuously. -/
theorem DrainState.StrongNewNameShape.init (decls : Typed.Decls)
    (pending : Std.HashSet (Global × Array Typ)) :
    DrainState.StrongNewNameShape decls
      { pending, seen := {}, mono := {}, newFunctions := #[], newDataTypes := #[] } := by
  refine ⟨?_, ?_⟩
  · intro f hf
    simp only [Array.not_mem_empty] at hf
  · intro dt hdt
    simp only [Array.not_mem_empty] at hdt

/-- Drain invariant: every pushed `newFunctions`/`newDataTypes` entry has a
witness `(g, args) ∈ st.seen` whose mangled key equals the entry's name.
Used together with `StrongNewNameShape` (typed-origin link) and
`SeenSubsetMono` (seen → mono entry) to recover a backward `mono[(g, args)]?
= some entry.name` mapping for any `f ∈ newFunctions` / `dt ∈ newDataTypes`. -/
def DrainState.NewDtFnInSeen (st : DrainState) : Prop :=
  (∀ f ∈ st.newFunctions,
    ∃ (g : Global) (args : Array Typ),
      f.name = concretizeName g args ∧ (g, args) ∈ st.seen) ∧
  (∀ dt ∈ st.newDataTypes,
    ∃ (g : Global) (args : Array Typ),
      dt.name = concretizeName g args ∧ (g, args) ∈ st.seen)

/-- Empty initial state satisfies `NewDtFnInSeen` vacuously. -/
theorem DrainState.NewDtFnInSeen.init
    (pending : Std.HashSet (Global × Array Typ)) :
    DrainState.NewDtFnInSeen
      { pending, seen := {}, mono := {}, newFunctions := #[], newDataTypes := #[] } := by
  refine ⟨?_, ?_⟩
  · intro f hf; simp only [Array.not_mem_empty] at hf
  · intro dt hdt; simp only [Array.not_mem_empty] at hdt

/-- FullyMono-implied structural correspondence: each drained newDt name
equals a source dt-key, with matching constructor nameHeads. -/
def NewDtBridge (typedDecls : Typed.Decls) (newDataTypes : Array DataType) : Prop :=
  ∀ dt ∈ newDataTypes,
    ∃ (g : Global) (orig : DataType),
      typedDecls.getByKey g = some (.dataType orig) ∧
      dt.name = g ∧
      dt.constructors.map (·.nameHead) = orig.constructors.map (·.nameHead)

/-- FullyMono-implied correspondence for functions. -/
def NewFnBridge (typedDecls : Typed.Decls) (newFunctions : Array Typed.Function) : Prop :=
  ∀ f ∈ newFunctions,
    ∃ (g : Global) (orig : Typed.Function),
      typedDecls.getByKey g = some (.function orig) ∧
      f.name = g

/-! ## Drain-invariant scaffolding for `drainMono_coversTypesInTds` (Stage 1)

The L3 sub-blocker `drainMono_coversTypesInTds` (in `Proofs/ConcretizeSound.lean`)
needs: under `FullyMonomorphic`, every `.app g args` subterm in `tds`-decls
or in `drained.newFunctions` / `drained.newDataTypes` has a `mono`-map entry
`(g, args) ↦ g'` whose `g'` is itself a tds dt-key.

The key non-trivial fact is that drain processes every `(g, args)` that
appears in the `concretizeSeed` (and recursively, every `(g', args')`
discovered by inserting templates) into both `seen` and `mono` simultaneously.

We decompose the target into TWO drain-state invariants whose composition
discharges the closure (Stage 2 will compose these; this file is Stage-1
scaffolding only):

  * `SeenSubsetMono` — every `(g, args) ∈ st.seen` has
    `st.mono[(g, args)]?.isSome`. Direct consequence of `concretizeDrainEntry`'s
    structure (it inserts into `seen` and `mono` in lockstep when it doesn't
    short-circuit on a re-seen entry).

  * `AppsReached tds` — every `.app g args` subterm reachable in `tds`-types
    or `st.newFunctions` / `st.newDataTypes` has `(g, args) ∈ st.seen ∪
    st.pending`. At drain termination (`pending = ∅`), this collapses to
    `(g, args) ∈ seen`; combined with `SeenSubsetMono` we get a `mono` entry.

Stage 1 (this file) defines both predicates, proves them at the initial
state, and proves drain-step preservation of `SeenSubsetMono`. Stage 2 will
prove drain-step preservation of `AppsReached` (its hardest piece is showing
that `concretizeDrainEntry`'s `pending'` discoveries cover the new types
introduced by the specialization step) and assemble the closure inside
`Proofs/ConcretizeSound.lean`. -/

/-- Structural predicate on a type: every `.app g args` subterm has `(g, args)`
satisfying the predicate `P`. Recurses through `.pointer`, `.tuple`, `.array`,
`.function`, and `.app` argument positions. -/
inductive Typ.AllAppsP (P : Global → Array Typ → Prop) : Typ → Prop
  | unit    : Typ.AllAppsP P .unit
  | field   : Typ.AllAppsP P .field
  | mvar n  : Typ.AllAppsP P (.mvar n)
  | ref g   : Typ.AllAppsP P (.ref g)
  | pointer {inner} (h : Typ.AllAppsP P inner) :
      Typ.AllAppsP P (.pointer inner)
  | tuple {ts} (h : ∀ t ∈ ts.toList, Typ.AllAppsP P t) :
      Typ.AllAppsP P (.tuple ts)
  | array {t n} (h : Typ.AllAppsP P t) :
      Typ.AllAppsP P (.array t n)
  | function {ins out}
      (hi : ∀ t ∈ ins, Typ.AllAppsP P t)
      (ho : Typ.AllAppsP P out) :
      Typ.AllAppsP P (.function ins out)
  | app {g args}
      (hsub : ∀ t ∈ args.toList, Typ.AllAppsP P t)
      (hin : P g args) :
      Typ.AllAppsP P (.app g args)

/-- Drain invariant: every `(g, args)` recorded in `st.seen` has a corresponding
`st.mono` entry `(g, args) ↦ g'` for some `g'`.

Proof intuition: `concretizeDrainEntry` either short-circuits on a re-seen
entry (no change to either set) or inserts into `seen` AND `mono` together
on the success path (both `.function` and `.dataType` arms). The error
arm (`.constructor`/`templateNotFound`/`wrongNumArgs`) doesn't change the
state. So step-wise preservation is direct.

Combined with `AppsReached`, gives `mono` coverage of every reachable
`.app` instance at drain termination. -/
def DrainState.SeenSubsetMono (st : DrainState) : Prop :=
  ∀ (g : Global) (args : Array Typ),
    (g, args) ∈ st.seen → st.mono[(g, args)]? = some (concretizeName g args)

/-- The empty initial drain state satisfies `SeenSubsetMono` vacuously. -/
theorem DrainState.SeenSubsetMono.init
    (pending : Std.HashSet (Global × Array Typ)) :
    DrainState.SeenSubsetMono
      { pending, seen := {}, mono := {}, newFunctions := #[], newDataTypes := #[] } := by
  intro g args hseen
  -- `(g, args) ∈ ({} : HashSet _)` is `False`.
  exact absurd hseen Std.HashSet.not_mem_empty

/-- `concretizeDrainEntry` preserves `SeenSubsetMono`: every successful step
either (a) short-circuits (state unchanged), (b) errors (no `.ok` output),
or (c) inserts `(name, args)` into both `seen` AND `mono` (the latter mapped
to `concretizeName name args`). The `.constructor` arm errors. -/
theorem concretizeDrainEntry_preserves_SeenSubsetMono
    {decls : Typed.Decls} {state state' : DrainState}
    (hinv : state.SeenSubsetMono) (entry : Global × Array Typ)
    (hstep : concretizeDrainEntry decls state entry = .ok state') :
    state'.SeenSubsetMono := by
  unfold concretizeDrainEntry at hstep
  simp only [bind, Except.bind, pure, Except.pure] at hstep
  by_cases hseen : state.seen.contains (entry.1, entry.2)
  · -- Short-circuit: state unchanged.
    simp [hseen] at hstep
    rw [← hstep]; exact hinv
  · simp [hseen] at hstep
    split at hstep
    · rename_i f hf_get
      split at hstep
      · -- success branch (params.length = args.size): inserts into seen + mono.
        simp only [Except.ok.injEq] at hstep
        rw [← hstep]
        intro g args hg
        simp only at hg
        rw [Std.HashSet.mem_insert] at hg
        rcases hg with hbeq | hold
        · have heq : (entry.1, entry.2) = (g, args) := LawfulBEq.eq_of_beq hbeq
          obtain ⟨he1, he2⟩ := Prod.mk.inj heq
          show (state.mono.insert (entry.1, entry.2) _)[(g, args)]? = _
          rw [he1, he2, Std.HashMap.getElem?_insert_self]
        · have hold_eq := hinv g args hold
          show (state.mono.insert (entry.1, entry.2)
                (concretizeName entry.1 entry.2))[(g, args)]? = _
          rw [Std.HashMap.getElem?_insert]
          split
          · rename_i hbeq
            have heq : (entry.1, entry.2) = (g, args) := LawfulBEq.eq_of_beq hbeq
            obtain ⟨he1, he2⟩ := Prod.mk.inj heq
            rw [he1, he2]
          · exact hold_eq
      · -- arity mismatch: throws.
        cases hstep
    · rename_i dt hdt_get
      split at hstep
      · -- success branch.
        simp only [Except.ok.injEq] at hstep
        rw [← hstep]
        intro g args hg
        simp only at hg
        rw [Std.HashSet.mem_insert] at hg
        rcases hg with hbeq | hold
        · have heq : (entry.1, entry.2) = (g, args) := LawfulBEq.eq_of_beq hbeq
          obtain ⟨he1, he2⟩ := Prod.mk.inj heq
          show (state.mono.insert (entry.1, entry.2) _)[(g, args)]? = _
          rw [he1, he2, Std.HashMap.getElem?_insert_self]
        · have hold_eq := hinv g args hold
          show (state.mono.insert (entry.1, entry.2)
                (concretizeName entry.1 entry.2))[(g, args)]? = _
          rw [Std.HashMap.getElem?_insert]
          split
          · rename_i hbeq
            have heq : (entry.1, entry.2) = (g, args) := LawfulBEq.eq_of_beq hbeq
            obtain ⟨he1, he2⟩ := Prod.mk.inj heq
            rw [he1, he2]
          · exact hold_eq
      · -- arity mismatch.
        cases hstep
    · -- `.constructor` / `none` / `some (.constructor _ _)`: throws `templateNotFound`.
      cases hstep

/-- Folding `concretizeDrainEntry` over a list preserves `SeenSubsetMono`. -/
theorem concretizeDrainEntry_list_foldlM_preserves_SeenSubsetMono
    {decls : Typed.Decls}
    (L : List (Global × Array Typ))
    (state0 state' : DrainState)
    (hinv0 : state0.SeenSubsetMono)
    (hstep : L.foldlM (concretizeDrainEntry decls) state0 = .ok state') :
    state'.SeenSubsetMono := by
  induction L generalizing state0 with
  | nil =>
    simp only [List.foldlM, pure, Except.pure, Except.ok.injEq] at hstep
    rw [← hstep]; exact hinv0
  | cons hd tl ih =>
    simp only [List.foldlM, bind, Except.bind] at hstep
    split at hstep
    · cases hstep
    · rename_i s'' hs''
      have hinv1 : s''.SeenSubsetMono :=
        concretizeDrainEntry_preserves_SeenSubsetMono hinv0 hd hs''
      exact ih s'' hinv1 hstep

/-- `concretizeDrainIter` preserves `SeenSubsetMono`. The iter pre-pass clears
`pending`; this doesn't affect `seen` or `mono`, so the invariant carries. -/
theorem concretizeDrainIter_preserves_SeenSubsetMono
    {decls : Typed.Decls} {state state' : DrainState}
    (hinv : state.SeenSubsetMono)
    (hstep : concretizeDrainIter decls state = .ok state') :
    state'.SeenSubsetMono := by
  unfold concretizeDrainIter at hstep
  rw [← Array.foldlM_toList] at hstep
  let state0 : DrainState := { state with pending := ∅ }
  have hinv0 : state0.SeenSubsetMono := hinv
  exact concretizeDrainEntry_list_foldlM_preserves_SeenSubsetMono
    state.pending.toArray.toList state0 state' hinv0 hstep

/-- `concretizeDrain` preserves `SeenSubsetMono`. Mirrors the
`concretize_drain_preserves_NewNameShape` fuel-induction structure. -/
theorem concretize_drain_preserves_SeenSubsetMono
    {decls : Typed.Decls} (fuel : Nat) (init : DrainState)
    (hinv : init.SeenSubsetMono)
    {drained : DrainState}
    (hdrain : concretizeDrain decls fuel init = .ok drained) :
    drained.SeenSubsetMono := by
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
        have hinv' : state'.SeenSubsetMono :=
          concretizeDrainIter_preserves_SeenSubsetMono hinv hstate'
        exact ih state' hinv' hdrain

/-- Drain invariant requiring `seen ∪ pending` to cover every `.app g args`
subterm of every type appearing in `tds` (function inputs/outputs, dt-ctor
argtypes) and every type in `st.newFunctions` / `st.newDataTypes`.

At drain termination (`pending = ∅`), this collapses to `seen`-coverage;
chained with `SeenSubsetMono` it gives `mono`-coverage. -/
def DrainState.AppsReached (tds : Typed.Decls) (st : DrainState) : Prop :=
  let typOk : Typ → Prop :=
    Typ.AllAppsP (fun g args => (g, args) ∈ st.seen ∨ (g, args) ∈ st.pending)
  (∀ key d, tds.getByKey key = some d →
      match d with
      | .function f =>
          (∀ lt ∈ f.inputs, typOk lt.snd) ∧ typOk f.output
      | .dataType dt =>
          ∀ c ∈ dt.constructors, ∀ ty ∈ c.argTypes, typOk ty
      | .constructor _ c =>
          ∀ ty ∈ c.argTypes, typOk ty) ∧
  (∀ dt ∈ st.newDataTypes, ∀ c ∈ dt.constructors, ∀ ty ∈ c.argTypes, typOk ty) ∧
  (∀ f ∈ st.newFunctions,
    (∀ lt ∈ f.inputs, typOk lt.snd) ∧ typOk f.output)

/-! ### Structural lemmas on `collectInTyp` (Stage 2 helpers).

These prove (a) monotonicity (every member of `seen` survives), and
(b) coverage (every `.app` subterm of `t` is collected). The latter is the
crux of `concretizeSeed_covers_tds_apps`. -/

/-- `xs.attach.foldl (fun s ⟨t, _⟩ => collectInTyp s t) seen` collapses to
`xs.foldl collectInTyp seen` (the `.attach` is only there for termination). -/
private theorem collectInTyp_attach_foldl_eq (xs : Array Typ)
    (seen : Std.HashSet (Global × Array Typ)) :
    (xs.attach.foldl (fun s ⟨t, _⟩ => collectInTyp s t) seen) =
    xs.foldl collectInTyp seen := Array.foldl_attach

/-- List-foldl preserves membership when each element step does. Non-recursive
in `collectInTyp_subset`; the per-element step is passed in. -/
private theorem collectInTyp_foldl_list_subset
    (p : Global × Array Typ) :
    ∀ (l : List Typ) (seen : Std.HashSet (Global × Array Typ)),
      (∀ t ∈ l, ∀ s, p ∈ s → p ∈ collectInTyp s t) →
      p ∈ seen → p ∈ l.foldl collectInTyp seen
  | [], _, _, h => h
  | hd :: tl, seen, hl, h => by
    simp only [List.foldl_cons]
    exact collectInTyp_foldl_list_subset p tl (collectInTyp seen hd)
      (fun t ht s hs => hl t (List.mem_cons.mpr (Or.inr ht)) s hs)
      (hl hd List.mem_cons_self seen h)

/-- Monotonicity of `collectInTyp`: every existing pair survives. -/
private theorem collectInTyp_subset :
    ∀ (t : Typ) (seen : Std.HashSet (Global × Array Typ)) (p : Global × Array Typ),
      p ∈ seen → p ∈ collectInTyp seen t
  | .unit, _, _, h => by unfold collectInTyp; exact h
  | .field, _, _, h => by unfold collectInTyp; exact h
  | .mvar _, _, _, h => by unfold collectInTyp; exact h
  | .ref _, _, _, h => by unfold collectInTyp; exact h
  | .pointer inner, seen, p, h => by
    unfold collectInTyp; exact collectInTyp_subset inner seen p h
  | .array t _, seen, p, h => by
    unfold collectInTyp; exact collectInTyp_subset t seen p h
  | .tuple ts, seen, p, h => by
    unfold collectInTyp
    rw [collectInTyp_attach_foldl_eq]
    -- foldl over `collectInTyp` preserves membership.
    have :=
      Array.foldl_induction
        (as := ts)
        (motive := fun (_ : Nat) (s : Std.HashSet (Global × Array Typ)) => p ∈ s)
        (init := seen)
        (f := collectInTyp)
        h
        (fun i s hs => by
          have hmem : ts[i] ∈ ts := Array.getElem_mem _
          exact collectInTyp_subset ts[i] s p hs)
    exact this
  | .function ins out, seen, p, h => by
    unfold collectInTyp
    rw [show (ins.attach.foldl (fun s ⟨t, _⟩ => collectInTyp s t) seen) =
            ins.foldl collectInTyp seen from List.foldl_attach]
    have hfold : p ∈ ins.foldl collectInTyp seen :=
      collectInTyp_foldl_list_subset p ins seen
        (fun t ht s hs => collectInTyp_subset t s p hs) h
    exact collectInTyp_subset out _ p hfold
  | .app g args, seen, p, h => by
    unfold collectInTyp
    rw [collectInTyp_attach_foldl_eq]
    have hfold : p ∈ args.foldl collectInTyp seen :=
      Array.foldl_induction
        (as := args)
        (motive := fun (_ : Nat) (s : Std.HashSet (Global × Array Typ)) => p ∈ s)
        (init := seen)
        (f := collectInTyp)
        h
        (fun i s hs => by
          have hmem : args[i] ∈ args := Array.getElem_mem _
          exact collectInTyp_subset args[i] s p hs)
    rw [Std.HashSet.mem_insert]; exact Or.inr hfold
  termination_by t => sizeOf t
  decreasing_by
    all_goals first
      | decreasing_tactic
      | (have := Array.sizeOf_lt_of_mem hmem; grind)
      | (have := List.sizeOf_lt_of_mem ‹_ ∈ _›; grind)
      | (have := List.sizeOf_lt_of_mem (List.mem_cons_self); grind)
      | (have := List.sizeOf_lt_of_mem (List.mem_cons.mpr (Or.inr ‹_›)); grind)

/-- Array-foldl version of `collectInTyp` monotonicity. -/
private theorem collectInTyp_foldl_array_subset
    (xs : Array Typ) (seen : Std.HashSet (Global × Array Typ))
    (p : Global × Array Typ) (h : p ∈ seen) :
    p ∈ xs.foldl collectInTyp seen :=
  Array.foldl_induction
    (as := xs)
    (motive := fun (_ : Nat) (s : Std.HashSet (Global × Array Typ)) => p ∈ s)
    (init := seen) (f := collectInTyp) h
    (fun i s hs => collectInTyp_subset xs[i] s p hs)

/-- Weakening: if `P → Q` pointwise then `AllAppsP P t → AllAppsP Q t`. -/
theorem Typ.AllAppsP.weaken {P Q : Global → Array Typ → Prop}
    (hweak : ∀ g args, P g args → Q g args) :
    ∀ {t : Typ}, Typ.AllAppsP P t → Typ.AllAppsP Q t := by
  intro t ht
  induction ht with
  | unit => exact .unit
  | field => exact .field
  | mvar n => exact .mvar n
  | ref g => exact .ref g
  | pointer _ ih => exact .pointer ih
  | tuple _ ih => exact .tuple ih
  | array _ ih => exact .array ih
  | function _ _ ihi iho => exact .function ihi iho
  | app hsub hin ihsub => exact .app ihsub (hweak _ _ hin)

/-- Monotonicity of `collectInTypedTerm`: every existing pair survives. -/
private theorem collectInTypedTerm_subset :
    ∀ (t : Typed.Term) (seen : Std.HashSet (Global × Array Typ))
      (p : Global × Array Typ),
      p ∈ seen → p ∈ collectInTypedTerm seen t
  | .unit τ _, seen, p, h => by
    unfold collectInTypedTerm; exact collectInTyp_subset τ seen p h
  | .var τ _ _, seen, p, h => by
    unfold collectInTypedTerm; exact collectInTyp_subset τ seen p h
  | .ref τ _ _ tArgs, seen, p, h => by
    unfold collectInTypedTerm
    exact collectInTyp_foldl_array_subset tArgs (collectInTyp seen τ) p
      (collectInTyp_subset τ seen p h)
  | .field τ _ _, seen, p, h => by
    unfold collectInTypedTerm; exact collectInTyp_subset τ seen p h
  | .tuple τ _ ts, seen, p, h => by
    unfold collectInTypedTerm
    rw [show (ts.attach.foldl (fun s ⟨t, _⟩ => collectInTypedTerm s t)
                              (collectInTyp seen τ)) =
            ts.foldl collectInTypedTerm (collectInTyp seen τ) from Array.foldl_attach]
    have h1 := collectInTyp_subset τ seen p h
    exact Array.foldl_induction (as := ts)
      (motive := fun _ s => p ∈ s) (init := collectInTyp seen τ)
      (f := collectInTypedTerm) h1
      (fun i s hs => by
        have hmem : ts[i] ∈ ts := Array.getElem_mem _
        exact collectInTypedTerm_subset ts[i] s p hs)
  | .array τ _ ts, seen, p, h => by
    unfold collectInTypedTerm
    rw [show (ts.attach.foldl (fun s ⟨t, _⟩ => collectInTypedTerm s t)
                              (collectInTyp seen τ)) =
            ts.foldl collectInTypedTerm (collectInTyp seen τ) from Array.foldl_attach]
    have h1 := collectInTyp_subset τ seen p h
    exact Array.foldl_induction (as := ts)
      (motive := fun _ s => p ∈ s) (init := collectInTyp seen τ)
      (f := collectInTypedTerm) h1
      (fun i s hs => by
        have hmem : ts[i] ∈ ts := Array.getElem_mem _
        exact collectInTypedTerm_subset ts[i] s p hs)
  | .ret τ _ r, seen, p, h => by
    unfold collectInTypedTerm
    exact collectInTypedTerm_subset r (collectInTyp seen τ) p
      (collectInTyp_subset τ seen p h)
  | .let τ _ _ v b, seen, p, h => by
    unfold collectInTypedTerm
    have h1 := collectInTyp_subset τ seen p h
    have h2 := collectInTypedTerm_subset v (collectInTyp seen τ) p h1
    exact collectInTypedTerm_subset b _ p h2
  | .match τ _ scrut bs, seen, p, h => by
    unfold collectInTypedTerm
    have h1 := collectInTyp_subset τ seen p h
    have h2 := collectInTypedTerm_subset scrut _ p h1
    -- bs : List (Pattern × Term); convert attach.foldl to plain foldl, then
    -- use List.foldlRecOn so each step has `pb ∈ bs` for termination.
    show p ∈ bs.attach.foldl (fun s ⟨(_, b), _⟩ => collectInTypedTerm s b)
              (collectInTypedTerm (collectInTyp seen τ) scrut)
    rw [show (bs.attach.foldl (fun s ⟨(_, b), _⟩ => collectInTypedTerm s b)
                              (collectInTypedTerm (collectInTyp seen τ) scrut)) =
            bs.foldl (fun s pb => collectInTypedTerm s pb.snd)
                     (collectInTypedTerm (collectInTyp seen τ) scrut) from
        List.foldl_attach (l := bs) (f := fun s pb => collectInTypedTerm s pb.snd)
          (b := collectInTypedTerm (collectInTyp seen τ) scrut)]
    exact List.foldlRecOn bs (fun s pb => collectInTypedTerm s pb.snd) h2
      (fun s hs pb hpb => by
        have hmem : pb ∈ bs := hpb
        exact collectInTypedTerm_subset pb.snd s p hs)
  | .app τ _ _ tArgs args _, seen, p, h => by
    unfold collectInTypedTerm
    have h1 := collectInTyp_subset τ seen p h
    have h2 := collectInTyp_foldl_array_subset tArgs (collectInTyp seen τ) p h1
    -- args : List Typed.Term; convert attach.foldl to plain foldl, then induct.
    rw [show (args.attach.foldl (fun s ⟨a, _⟩ => collectInTypedTerm s a)
                                (tArgs.foldl collectInTyp (collectInTyp seen τ))) =
            args.foldl collectInTypedTerm
                       (tArgs.foldl collectInTyp (collectInTyp seen τ)) from
        List.foldl_attach]
    exact List.foldlRecOn args collectInTypedTerm h2
      (fun s hs a ha => by
        have hmem : a ∈ args := ha
        exact collectInTypedTerm_subset a s p hs)
  | .add τ _ a b, seen, p, h
  | .sub τ _ a b, seen, p, h
  | .mul τ _ a b, seen, p, h
  | .u8Xor τ _ a b, seen, p, h
  | .u8Add τ _ a b, seen, p, h
  | .u8Sub τ _ a b, seen, p, h
  | .u8And τ _ a b, seen, p, h
  | .u8Or τ _ a b, seen, p, h
  | .u8LessThan τ _ a b, seen, p, h
  | .u32LessThan τ _ a b, seen, p, h => by
    unfold collectInTypedTerm
    have h1 := collectInTyp_subset τ seen p h
    have h2 := collectInTypedTerm_subset a _ p h1
    exact collectInTypedTerm_subset b _ p h2
  | .eqZero τ _ a, seen, p, h
  | .store τ _ a, seen, p, h
  | .load τ _ a, seen, p, h
  | .ptrVal τ _ a, seen, p, h
  | .u8BitDecomposition τ _ a, seen, p, h
  | .u8ShiftLeft τ _ a, seen, p, h
  | .u8ShiftRight τ _ a, seen, p, h
  | .ioGetInfo τ _ a, seen, p, h => by
    unfold collectInTypedTerm
    exact collectInTypedTerm_subset a _ p (collectInTyp_subset τ seen p h)
  | .proj τ _ a _, seen, p, h
  | .get τ _ a _, seen, p, h
  | .slice τ _ a _ _, seen, p, h => by
    unfold collectInTypedTerm
    exact collectInTypedTerm_subset a _ p (collectInTyp_subset τ seen p h)
  | .set τ _ a _ v, seen, p, h => by
    unfold collectInTypedTerm
    have h1 := collectInTyp_subset τ seen p h
    have h2 := collectInTypedTerm_subset a _ p h1
    exact collectInTypedTerm_subset v _ p h2
  | .assertEq τ _ a b r, seen, p, h => by
    unfold collectInTypedTerm
    have h1 := collectInTyp_subset τ seen p h
    have h2 := collectInTypedTerm_subset a _ p h1
    have h3 := collectInTypedTerm_subset b _ p h2
    exact collectInTypedTerm_subset r _ p h3
  | .ioSetInfo τ _ k i l r, seen, p, h => by
    unfold collectInTypedTerm
    have h1 := collectInTyp_subset τ seen p h
    have h2 := collectInTypedTerm_subset k _ p h1
    have h3 := collectInTypedTerm_subset i _ p h2
    have h4 := collectInTypedTerm_subset l _ p h3
    exact collectInTypedTerm_subset r _ p h4
  | .ioRead τ _ i _, seen, p, h => by
    unfold collectInTypedTerm
    exact collectInTypedTerm_subset i _ p (collectInTyp_subset τ seen p h)
  | .ioWrite τ _ d r, seen, p, h => by
    unfold collectInTypedTerm
    have h1 := collectInTyp_subset τ seen p h
    have h2 := collectInTypedTerm_subset d _ p h1
    exact collectInTypedTerm_subset r _ p h2
  | .debug τ _ _ t r, seen, p, h => by
    unfold collectInTypedTerm
    have h1 := collectInTyp_subset τ seen p h
    have hmid : p ∈ (match t with
        | some t => collectInTypedTerm (collectInTyp seen τ) t
        | none => collectInTyp seen τ) := by
      cases t with
      | none => exact h1
      | some sub => exact collectInTypedTerm_subset sub _ p h1
    exact collectInTypedTerm_subset r _ p hmid
  termination_by t => sizeOf t
  decreasing_by
    all_goals first
      | decreasing_tactic
      | (have : ∀ {α} [SizeOf α] (a : α), sizeOf a < sizeOf (some a) := by
           intros; show _ < 1 + _; omega
         grind)
      | (have := Array.sizeOf_lt_of_mem hmem; grind)
      | (have := List.sizeOf_lt_of_mem ‹_ ∈ _›; grind)
      | (have := List.sizeOf_lt_of_mem (List.mem_cons_self); grind)
      | (have := List.sizeOf_lt_of_mem (List.mem_cons.mpr (Or.inr ‹_›)); grind)

/-- Monotonicity of `collectCalls`: every existing pair survives. -/
private theorem collectCalls_subset (decls : Typed.Decls) :
    ∀ (t : Typed.Term) (seen : Std.HashSet (Global × Array Typ))
      (p : Global × Array Typ),
      p ∈ seen → p ∈ collectCalls decls seen t
  | .unit _ _, _, _, h => by unfold collectCalls; exact h
  | .var _ _ _, _, _, h => by unfold collectCalls; exact h
  | .field _ _ _, _, _, h => by unfold collectCalls; exact h
  | .ref _ _ g tArgs, seen, p, h => by
    unfold collectCalls
    split
    · exact h
    · split
      · rw [Std.HashSet.mem_insert]; exact Or.inr h
      · rw [Std.HashSet.mem_insert]; exact Or.inr h
      · exact h
  | .tuple _ _ ts, seen, p, h
  | .array _ _ ts, seen, p, h => by
    unfold collectCalls
    rw [show (ts.attach.foldl (fun s ⟨t, _⟩ => collectCalls decls s t) seen) =
            ts.foldl (collectCalls decls) seen from Array.foldl_attach]
    exact Array.foldl_induction (as := ts)
      (motive := fun _ s => p ∈ s) (init := seen)
      (f := collectCalls decls) h
      (fun i s hs => by
        have hmem : ts[i] ∈ ts := Array.getElem_mem _
        exact collectCalls_subset decls ts[i] s p hs)
  | .ret _ _ r, seen, p, h => by
    unfold collectCalls; exact collectCalls_subset decls r seen p h
  | .let _ _ _ v b, seen, p, h => by
    unfold collectCalls
    exact collectCalls_subset decls b _ p (collectCalls_subset decls v seen p h)
  | .match _ _ scrut bs, seen, p, h => by
    unfold collectCalls
    have h1 := collectCalls_subset decls scrut seen p h
    show p ∈ bs.attach.foldl (fun s ⟨(_, b), _⟩ => collectCalls decls s b)
              (collectCalls decls seen scrut)
    rw [show (bs.attach.foldl (fun s ⟨(_, b), _⟩ => collectCalls decls s b)
                              (collectCalls decls seen scrut)) =
            bs.foldl (fun s pb => collectCalls decls s pb.snd)
                     (collectCalls decls seen scrut) from
        List.foldl_attach (l := bs)
          (f := fun s pb => collectCalls decls s pb.snd)
          (b := collectCalls decls seen scrut)]
    exact List.foldlRecOn bs (fun s pb => collectCalls decls s pb.snd) h1
      (fun s hs pb hpb => by
        have hmem : pb ∈ bs := hpb
        exact collectCalls_subset decls pb.snd s p hs)
  | .app _ _ g tArgs args _, seen, p, h => by
    unfold collectCalls
    have hargs0 : p ∈ args.foldl (collectCalls decls) seen :=
      List.foldlRecOn args (collectCalls decls) h
        (fun s hs a ha => by
          have hmem : a ∈ args := ha
          exact collectCalls_subset decls a s p hs)
    have hargs : p ∈ args.attach.foldl
        (fun s ⟨a, _⟩ => collectCalls decls s a) seen := by
      rw [show (args.attach.foldl (fun s ⟨a, _⟩ => collectCalls decls s a) seen) =
              args.foldl (collectCalls decls) seen from List.foldl_attach]
      exact hargs0
    split
    · exact hargs
    · split
      · rw [Std.HashSet.mem_insert]; exact Or.inr hargs
      · rw [Std.HashSet.mem_insert]; exact Or.inr hargs
      · exact hargs
  | .add _ _ a b, seen, p, h
  | .sub _ _ a b, seen, p, h
  | .mul _ _ a b, seen, p, h
  | .u8Xor _ _ a b, seen, p, h
  | .u8Add _ _ a b, seen, p, h
  | .u8Sub _ _ a b, seen, p, h
  | .u8And _ _ a b, seen, p, h
  | .u8Or _ _ a b, seen, p, h
  | .u8LessThan _ _ a b, seen, p, h
  | .u32LessThan _ _ a b, seen, p, h => by
    unfold collectCalls
    exact collectCalls_subset decls b _ p (collectCalls_subset decls a seen p h)
  | .eqZero _ _ a, seen, p, h
  | .store _ _ a, seen, p, h
  | .load _ _ a, seen, p, h
  | .ptrVal _ _ a, seen, p, h
  | .u8BitDecomposition _ _ a, seen, p, h
  | .u8ShiftLeft _ _ a, seen, p, h
  | .u8ShiftRight _ _ a, seen, p, h
  | .ioGetInfo _ _ a, seen, p, h => by
    unfold collectCalls; exact collectCalls_subset decls a seen p h
  | .proj _ _ a _, seen, p, h
  | .get _ _ a _, seen, p, h
  | .slice _ _ a _ _, seen, p, h => by
    unfold collectCalls; exact collectCalls_subset decls a seen p h
  | .set _ _ a _ v, seen, p, h => by
    unfold collectCalls
    exact collectCalls_subset decls v _ p (collectCalls_subset decls a seen p h)
  | .assertEq _ _ a b r, seen, p, h => by
    unfold collectCalls
    have h1 := collectCalls_subset decls a seen p h
    have h2 := collectCalls_subset decls b _ p h1
    exact collectCalls_subset decls r _ p h2
  | .ioSetInfo _ _ k i l r, seen, p, h => by
    unfold collectCalls
    have h1 := collectCalls_subset decls k seen p h
    have h2 := collectCalls_subset decls i _ p h1
    have h3 := collectCalls_subset decls l _ p h2
    exact collectCalls_subset decls r _ p h3
  | .ioRead _ _ i _, seen, p, h => by
    unfold collectCalls; exact collectCalls_subset decls i seen p h
  | .ioWrite _ _ d r, seen, p, h => by
    unfold collectCalls
    exact collectCalls_subset decls r _ p (collectCalls_subset decls d seen p h)
  | .debug _ _ _ t r, seen, p, h => by
    unfold collectCalls
    have hmid : p ∈ (match t with
        | some t => collectCalls decls seen t
        | none => seen) := by
      cases t with
      | none => exact h
      | some sub => exact collectCalls_subset decls sub seen p h
    exact collectCalls_subset decls r _ p hmid
  termination_by t => sizeOf t
  decreasing_by
    all_goals first
      | decreasing_tactic
      | (have : ∀ {α} [SizeOf α] (a : α), sizeOf a < sizeOf (some a) := by
           intros; show _ < 1 + _; omega
         grind)
      | (have := Array.sizeOf_lt_of_mem hmem; grind)
      | (have := List.sizeOf_lt_of_mem ‹_ ∈ _›; grind)
      | (have := List.sizeOf_lt_of_mem (List.mem_cons_self); grind)
      | (have := List.sizeOf_lt_of_mem (List.mem_cons.mpr (Or.inr ‹_›)); grind)

/-- `AllAppsP (∈ acc) t` lifts through any list-foldl over `collectInTyp`. -/
private theorem AllAppsP_foldl_list_mono (t : Typ) :
    ∀ (l : List Typ) (acc : Std.HashSet (Global × Array Typ)),
      Typ.AllAppsP (fun g args => (g, args) ∈ acc) t →
      Typ.AllAppsP (fun g args => (g, args) ∈ l.foldl collectInTyp acc) t
  | [], _, h => h
  | hd :: tl, acc, h => by
    simp only [List.foldl_cons]
    exact AllAppsP_foldl_list_mono t tl (collectInTyp acc hd)
      (h.weaken (fun g args ha => collectInTyp_subset hd acc _ ha))

/-- A `foldl collectInTyp` accumulator covers every `.app` subterm of every
fold input. Parameterised by an apps-collecting fact valid at ANY accumulator
(typically supplied by `collectInTyp_collects_apps`). -/
private theorem collectInTyp_foldl_covers (xs : Array Typ)
    (seen : Std.HashSet (Global × Array Typ))
    (helem : ∀ (t : Typ), t ∈ xs →
      ∀ (s : Std.HashSet (Global × Array Typ)),
        Typ.AllAppsP (fun g args => (g, args) ∈ collectInTyp s t) t) :
    ∀ (t : Typ), t ∈ xs →
      Typ.AllAppsP
        (fun g args => (g, args) ∈ xs.foldl collectInTyp seen) t := by
  intro t ht
  obtain ⟨i, hi, hi_eq⟩ := Array.mem_iff_getElem.mp ht
  have hgen :
      ∀ (k : Fin xs.size),
        Typ.AllAppsP
          (fun g args => (g, args) ∈ xs.foldl collectInTyp seen) xs[k.val] := by
    intro k
    have :=
      Array.foldl_induction
        (as := xs)
        (motive := fun (j : Nat) (s : Std.HashSet (Global × Array Typ)) =>
          ∀ (k' : Fin xs.size), k'.val < j →
            Typ.AllAppsP (fun g args => (g, args) ∈ s) xs[k'.val])
        (init := seen)
        (f := collectInTyp)
        (h0 := fun k' hk' => absurd hk' (Nat.not_lt_zero _))
        (hf := by
          intro j b hb
          intro k' hk'
          by_cases heq : k'.val = j.val
          · have hmem : xs[j.val] ∈ xs := Array.getElem_mem _
            have happs := helem xs[j.val] hmem b
            have hcast : xs[k'.val] = xs[j.val] := by congr 1
            rw [hcast]
            exact happs
          · have hlt : k'.val < j.val := by omega
            have ih := hb k' hlt
            exact ih.weaken (fun g args ha => collectInTyp_subset xs[j.val] b _ ha))
    exact this k k.isLt
  have hbound : i < xs.size := hi
  have := hgen ⟨i, hbound⟩
  rw [hi_eq] at this
  exact this

/-- List version of `collectInTyp_foldl_covers`. -/
private theorem collectInTyp_foldl_list_covers (xs : List Typ)
    (seen : Std.HashSet (Global × Array Typ))
    (helem : ∀ (t : Typ), t ∈ xs →
      ∀ (s : Std.HashSet (Global × Array Typ)),
        Typ.AllAppsP (fun g args => (g, args) ∈ collectInTyp s t) t) :
    ∀ (t : Typ), t ∈ xs →
      Typ.AllAppsP
        (fun g args => (g, args) ∈ xs.foldl collectInTyp seen) t := by
  -- Induction on xs, with the seen accumulator generalized.
  intro t ht
  induction xs generalizing seen with
  | nil => cases ht
  | cons hd tl ih =>
    rcases List.mem_cons.mp ht with heq | htl
    · subst heq
      simp only [List.foldl_cons]
      have hbase : Typ.AllAppsP
          (fun g args => (g, args) ∈ collectInTyp seen t) t :=
        helem t (List.mem_cons_self) seen
      exact AllAppsP_foldl_list_mono t tl (collectInTyp seen t) hbase
    · simp only [List.foldl_cons]
      apply ih (collectInTyp seen hd)
      · intro t' ht'_mem s
        exact helem t' (List.mem_cons.mpr (Or.inr ht'_mem)) s
      · exact htl

/-- `collectInTyp seen t` covers every `.app g args` subterm of `t`. -/
private theorem collectInTyp_collects_apps :
    ∀ (t : Typ) (seen : Std.HashSet (Global × Array Typ)),
      Typ.AllAppsP (fun g args => (g, args) ∈ collectInTyp seen t) t
  | .unit, _ => by unfold collectInTyp; exact .unit
  | .field, _ => by unfold collectInTyp; exact .field
  | .mvar n, _ => by unfold collectInTyp; exact .mvar n
  | .ref g, _ => by unfold collectInTyp; exact .ref g
  | .pointer inner, seen => by
    unfold collectInTyp
    exact .pointer (collectInTyp_collects_apps inner seen)
  | .array t n, seen => by
    unfold collectInTyp
    exact .array (collectInTyp_collects_apps t seen)
  | .tuple ts, seen => by
    unfold collectInTyp
    rw [collectInTyp_attach_foldl_eq]
    refine .tuple ?_
    intro t' ht'_mem
    have ht_arr : t' ∈ ts := Array.mem_toList_iff.mp ht'_mem
    exact collectInTyp_foldl_covers ts seen
      (fun t htmem s => by
        have := Array.sizeOf_lt_of_mem htmem
        exact collectInTyp_collects_apps t s) t' ht_arr
  | .function ins out, seen => by
    unfold collectInTyp
    rw [show (ins.attach.foldl (fun s ⟨t, _⟩ => collectInTyp s t) seen) =
            ins.foldl collectInTyp seen from List.foldl_attach]
    refine .function ?_ ?_
    · intro t' ht'_mem
      have hfold_covers :
          Typ.AllAppsP
            (fun g args => (g, args) ∈ ins.foldl collectInTyp seen) t' :=
        collectInTyp_foldl_list_covers ins seen
          (fun t htmem s => by
            have := List.sizeOf_lt_of_mem htmem
            exact collectInTyp_collects_apps t s) t' ht'_mem
      exact hfold_covers.weaken
        (fun g args ha => collectInTyp_subset out _ _ ha)
    · exact collectInTyp_collects_apps out _
  | .app g args, seen => by
    unfold collectInTyp
    rw [collectInTyp_attach_foldl_eq]
    refine .app ?_ ?_
    · intro t' ht'_mem
      have ht_arr : t' ∈ args := Array.mem_toList_iff.mp ht'_mem
      have hfold :=
        collectInTyp_foldl_covers args seen
          (fun t htmem s => by
            have := Array.sizeOf_lt_of_mem htmem
            exact collectInTyp_collects_apps t s) t' ht_arr
      exact hfold.weaken
        (fun g' args' ha => by rw [Std.HashSet.mem_insert]; exact Or.inr ha)
    · rw [Std.HashSet.mem_insert]; exact Or.inl BEq.rfl
  termination_by t => sizeOf t
  decreasing_by
    all_goals first
      | decreasing_tactic
      | (have := List.sizeOf_lt_of_mem (List.mem_cons_self); grind)
      | (have := List.sizeOf_lt_of_mem (List.mem_cons.mpr (Or.inr ‹_›)); grind)

/-! ### Stage-2 helpers for `concretizeSeed_covers_tds_apps`. -/

/-- Monotonicity through a `f.inputs.foldl` collecting via `lt.snd`. -/
private theorem concretizeSeed_inputs_foldl_subset
    (l : List (Local × Typ)) (acc : Std.HashSet (Global × Array Typ))
    (q : Global × Array Typ) (h : q ∈ acc) :
    q ∈ l.foldl (fun s lt => collectInTyp s lt.snd) acc := by
  induction l generalizing acc with
  | nil => exact h
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    exact ih (collectInTyp acc hd.snd) (collectInTyp_subset hd.snd acc q h)

/-- Monotonicity through `dt.constructors.foldl` collecting via inner argType-foldl. -/
private theorem concretizeSeed_dt_ctors_foldl_subset
    (l : List Constructor) (acc : Std.HashSet (Global × Array Typ))
    (q : Global × Array Typ) (h : q ∈ acc) :
    q ∈ l.foldl (fun s c => c.argTypes.foldl collectInTyp s) acc := by
  induction l generalizing acc with
  | nil => exact h
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    exact ih (hd.argTypes.foldl collectInTyp acc)
      (collectInTyp_foldl_list_subset q hd.argTypes acc
        (fun t _ s hs => collectInTyp_subset t s q hs) h)

/-- `AllAppsP (∈ acc) t` lifts through `f.inputs.foldl`. -/
private theorem AllAppsP_inputs_foldl_mono (t : Typ) :
    ∀ (l : List (Local × Typ)) (acc : Std.HashSet (Global × Array Typ)),
      Typ.AllAppsP (fun g args => (g, args) ∈ acc) t →
      Typ.AllAppsP (fun g args => (g, args) ∈
        l.foldl (fun s lt => collectInTyp s lt.snd) acc) t
  | [], _, h => h
  | hd :: tl, acc, h => by
    simp only [List.foldl_cons]
    exact AllAppsP_inputs_foldl_mono t tl _
      (h.weaken (fun g args ha => collectInTyp_subset hd.snd acc _ ha))

/-- `AllAppsP (∈ acc) t` lifts through `dt.constructors.foldl`. -/
private theorem AllAppsP_dt_ctors_foldl_mono (t : Typ) :
    ∀ (l : List Constructor) (acc : Std.HashSet (Global × Array Typ)),
      Typ.AllAppsP (fun g args => (g, args) ∈ acc) t →
      Typ.AllAppsP (fun g args => (g, args) ∈
        l.foldl (fun s c => c.argTypes.foldl collectInTyp s) acc) t
  | [], _, h => h
  | hd :: tl, acc, h => by
    simp only [List.foldl_cons]
    exact AllAppsP_dt_ctors_foldl_mono t tl _
      (h.weaken (fun g args ha =>
        collectInTyp_foldl_list_subset _ hd.argTypes acc
          (fun t' _ s hs => collectInTyp_subset t' s _ hs) ha))

/-- Coverage: for each `lt ∈ l`, `lt.snd`'s apps land in `l.foldl ...`. -/
private theorem AllAppsP_inputs_foldl_covers
    (l : List (Local × Typ)) (acc : Std.HashSet (Global × Array Typ))
    (lt : Local × Typ) (hlt : lt ∈ l) :
    Typ.AllAppsP (fun g args => (g, args) ∈
      l.foldl (fun s lt => collectInTyp s lt.snd) acc) lt.snd := by
  induction l generalizing acc with
  | nil => cases hlt
  | cons hd tl ih =>
    rcases List.mem_cons.mp hlt with heq | hin
    · subst heq
      simp only [List.foldl_cons]
      exact AllAppsP_inputs_foldl_mono lt.snd tl (collectInTyp acc lt.snd)
        (collectInTyp_collects_apps lt.snd acc)
    · simp only [List.foldl_cons]
      exact ih (collectInTyp acc hd.snd) hin

/-- Coverage: for each `c ∈ l` and `ty ∈ c.argTypes`, `ty`'s apps land in the foldl. -/
private theorem AllAppsP_dt_ctors_foldl_covers
    (l : List Constructor) (acc : Std.HashSet (Global × Array Typ))
    (c : Constructor) (hc : c ∈ l) (ty : Typ) (hty : ty ∈ c.argTypes) :
    Typ.AllAppsP (fun g args => (g, args) ∈
      l.foldl (fun s c => c.argTypes.foldl collectInTyp s) acc) ty := by
  induction l generalizing acc with
  | nil => cases hc
  | cons hd tl ih =>
    rcases List.mem_cons.mp hc with heq | hin
    · subst heq
      simp only [List.foldl_cons]
      have hbase : Typ.AllAppsP (fun g args => (g, args) ∈
          c.argTypes.foldl collectInTyp acc) ty :=
        collectInTyp_foldl_list_covers c.argTypes acc
          (fun t _ s => collectInTyp_collects_apps t s) ty hty
      exact AllAppsP_dt_ctors_foldl_mono ty tl _ hbase
    · simp only [List.foldl_cons]
      exact ih (hd.argTypes.foldl collectInTyp acc) hin

/-- Outer-step monotonicity: the step function in `concretizeSeed`'s foldl
preserves every `q ∈ acc`. -/
private theorem concretizeSeed_step_subset
    (decls : Typed.Decls) (kd : Global × Typed.Declaration)
    (acc : Std.HashSet (Global × Array Typ)) (q : Global × Array Typ)
    (hq : q ∈ acc) :
    q ∈ (match kd.snd with
         | .function f =>
           if f.params.isEmpty then
             let p1 := collectInTyp acc f.output
             let p2 := f.inputs.foldl (fun s (lt : Local × Typ) => collectInTyp s lt.snd) p1
             let p3 := collectInTypedTerm p2 f.body
             collectCalls decls p3 f.body
           else acc
         | .dataType dt =>
           if dt.params.isEmpty then
             dt.constructors.foldl (fun s (c : Constructor) => c.argTypes.foldl collectInTyp s) acc
           else acc
         | _ => acc) := by
  match h : kd.snd with
  | .function f =>
    by_cases hpe : f.params.isEmpty
    · simp only [hpe, ↓reduceIte]
      have h1 := collectInTyp_subset f.output _ q hq
      have h2 := concretizeSeed_inputs_foldl_subset f.inputs _ q h1
      have h3 := collectInTypedTerm_subset f.body _ q h2
      exact collectCalls_subset decls f.body _ q h3
    · simp only [hpe]; exact hq
  | .dataType dt =>
    by_cases hpe : dt.params.isEmpty
    · simp only [hpe, ↓reduceIte]
      exact concretizeSeed_dt_ctors_foldl_subset dt.constructors _ q hq
    · simp only [hpe]; exact hq
  | .constructor _ _ => exact hq

/-- Per-step coverage for `.function f` with `params.isEmpty`: after the step,
all apps in `f.output` and each `lt.snd ∈ f.inputs` are in the result. -/
private theorem concretizeSeed_function_step_covers
    (decls : Typed.Decls) (acc : Std.HashSet (Global × Array Typ))
    (f : Typed.Function) :
    let result :=
      let p1 := collectInTyp acc f.output
      let p2 := f.inputs.foldl (fun s lt => collectInTyp s lt.snd) p1
      let p3 := collectInTypedTerm p2 f.body
      collectCalls decls p3 f.body
    (∀ lt ∈ f.inputs, Typ.AllAppsP (fun g args => (g, args) ∈ result) lt.snd) ∧
    Typ.AllAppsP (fun g args => (g, args) ∈ result) f.output := by
  -- Lift any `AllAppsP (∈ p2)` claim through `collectInTypedTerm` and `collectCalls`.
  have lift_p2_to_result :
      ∀ {t : Typ},
        Typ.AllAppsP (fun g args => (g, args) ∈
          f.inputs.foldl (fun s lt => collectInTyp s lt.snd) (collectInTyp acc f.output)) t →
        Typ.AllAppsP (fun g args => (g, args) ∈
          (let p1 := collectInTyp acc f.output
           let p2 := f.inputs.foldl (fun s lt => collectInTyp s lt.snd) p1
           let p3 := collectInTypedTerm p2 f.body
           collectCalls decls p3 f.body)) t := by
    intro t h_p2
    have h_p3 := h_p2.weaken
      (fun g args ha => collectInTypedTerm_subset f.body _ _ ha)
    exact h_p3.weaken
      (fun g args ha => collectCalls_subset decls f.body _ _ ha)
  refine ⟨?_, ?_⟩
  · intro lt hlt
    exact lift_p2_to_result
      (AllAppsP_inputs_foldl_covers f.inputs (collectInTyp acc f.output) lt hlt)
  · -- f.output: collected by collectInTyp into p1, then preserved through inputs foldl.
    have h_p1 := collectInTyp_collects_apps f.output acc
    exact lift_p2_to_result
      (AllAppsP_inputs_foldl_mono f.output f.inputs (collectInTyp acc f.output) h_p1)

/-- Per-step coverage for `.dataType dt` with `params.isEmpty`: after the step,
all apps in every `c.argTypes` (for `c ∈ dt.constructors`) are in the result. -/
private theorem concretizeSeed_dataType_step_covers
    (acc : Std.HashSet (Global × Array Typ)) (dt : DataType) :
    let result := dt.constructors.foldl
      (fun s c => c.argTypes.foldl collectInTyp s) acc
    ∀ c ∈ dt.constructors, ∀ ty ∈ c.argTypes,
      Typ.AllAppsP (fun g args => (g, args) ∈ result) ty := by
  intro result c hc ty hty
  exact AllAppsP_dt_ctors_foldl_covers dt.constructors acc c hc ty hty

/-- Per-pair invariant for `concretizeSeed_covers_tds_apps`'s motive: the
type-positions inside `kd`'s decl are app-covered by `acc`. Phrased as an
∀-eq conjunction (rather than `match`) for easier weakening. -/
private def pairsCovered (acc : Std.HashSet (Global × Array Typ))
                         (kd : Global × Typed.Declaration) : Prop :=
  (∀ f, kd.snd = .function f →
    (∀ lt ∈ f.inputs, Typ.AllAppsP (fun g args => (g, args) ∈ acc) lt.snd) ∧
    Typ.AllAppsP (fun g args => (g, args) ∈ acc) f.output) ∧
  (∀ dt, kd.snd = .dataType dt →
    ∀ c ∈ dt.constructors, ∀ ty ∈ c.argTypes,
      Typ.AllAppsP (fun g args => (g, args) ∈ acc) ty)

/-- `pairsCovered` is monotone in `acc`. -/
private theorem pairsCovered.weaken
    (kd : Global × Typed.Declaration)
    {acc acc' : Std.HashSet (Global × Array Typ)}
    (hsub : ∀ q, q ∈ acc → q ∈ acc')
    (h : pairsCovered acc kd) : pairsCovered acc' kd := by
  obtain ⟨h_fn, h_dt⟩ := h
  refine ⟨?_, ?_⟩
  · intro f hf
    obtain ⟨h_in, h_out⟩ := h_fn f hf
    exact ⟨fun lt hlt => (h_in lt hlt).weaken (fun g args ha => hsub _ ha),
           h_out.weaken (fun g args ha => hsub _ ha)⟩
  · intro dt hdt c hc ty hty
    exact (h_dt dt hdt c hc ty hty).weaken (fun g args ha => hsub _ ha)

/-- Bridge sub-lemma (Stage-2 prerequisite): under FullyMono-derived
"all params empty" facts + ctor-companion presence, `concretizeSeed tds`
collects every `.app g args` subterm appearing in any type of any decl of
`tds`.

**SIG-FIX 2026-04-24** (was unconditionally false): `concretizeSeed` only
processes decls with `params.isEmpty` (skips `.constructor _ _` entries
entirely + skips polymorphic `.function`/`.dataType` entries). Without the
3 hypotheses below, the conclusion fails on:
  (a) polymorphic decls (when FullyMono is not in scope), or
  (b) `.constructor` entries whose companion `.dataType` lives at a
      different key (since the seed only iterates dt's via the key path,
      and ctor argTypes are subsumed by the companion dt iteration).

Caller `DrainState.AppsReached.init` (and downstream `drainMono_coversTypesInTds`)
derive the three hypotheses from `FullyMonomorphic t` + `t.checkAndSimplify = .ok tds`
via the L1 / CheckSound helpers (`mkDecls_dt_params_empty_of_fullyMonomorphic`,
`mkDecls_fn_params_empty_of_fullyMonomorphic`, `mkDecls_ctor_companion`).

BLOCKED ON: `Concretize.collectInTyp` / `collectInTypedTerm` correctness — a
structural induction over `Typ` showing that `collectInTyp seen t` returns a
superset of `seen` that includes every `.app g args ∈ t`, plus a similar
fact for `collectInTypedTerm` (recursing over `Typed.Term` via type
positions). The `concretizeSeed` outer-fold composes these. Stage-2 work,
estimated ~150 LoC. Uses HashSet `mem_insert` / `subset_insert` lemmas. -/
private theorem concretizeSeed_covers_tds_apps
    (tds : Typed.Decls)
    (hfn_params : ∀ key f, tds.getByKey key = some (.function f) →
                           f.params.isEmpty)
    (hdt_params : ∀ key dt, tds.getByKey key = some (.dataType dt) →
                            dt.params.isEmpty)
    (hctor_companion : ∀ key dt c,
        tds.getByKey key = some (.constructor dt c) →
        ∃ key', tds.getByKey key' = some (.dataType dt) ∧
                c ∈ dt.constructors) :
    let typOk : Typ → Prop :=
      Typ.AllAppsP (fun g args => (g, args) ∈ concretizeSeed tds)
    (∀ key d, tds.getByKey key = some d →
        match d with
        | .function f =>
            (∀ lt ∈ f.inputs, typOk lt.snd) ∧ typOk f.output
        | .dataType dt =>
            ∀ c ∈ dt.constructors, ∀ ty ∈ c.argTypes, typOk ty
        | .constructor _ c =>
            ∀ ty ∈ c.argTypes, typOk ty) := by
  intro typOk
  -- Motive-based foldl induction over `tds.pairs`. At step `j`, every prior
  -- pair `tds.pairs[k']` (k' < j) satisfies `pairsCovered acc`.
  have h_motive :=
    Array.foldl_induction
      (as := tds.pairs)
      (motive := fun (j : Nat) (acc : Std.HashSet (Global × Array Typ)) =>
        ∀ (k' : Fin tds.pairs.size), k'.val < j → pairsCovered acc tds.pairs[k'.val])
      (init := ({} : Std.HashSet (Global × Array Typ)))
      (f := fun pending p =>
        match p.snd with
        | .function f =>
          if f.params.isEmpty then
            let p1 := collectInTyp pending f.output
            let p2 := f.inputs.foldl
                       (fun s (lt : Local × Typ) => collectInTyp s lt.snd) p1
            let p3 := collectInTypedTerm p2 f.body
            collectCalls tds p3 f.body
          else pending
        | .dataType dt =>
          if dt.params.isEmpty then
            dt.constructors.foldl
              (fun s (c : Constructor) => c.argTypes.foldl collectInTyp s) pending
          else pending
        | _ => pending)
      (h0 := fun k' hk' => absurd hk' (Nat.not_lt_zero _))
      (hf := by
        intro j acc IH k' hk'
        by_cases heq : k'.val = j.val
        · -- New pair at index j: prove pairsCovered for tds.pairs[j].
          have hkd_eq : tds.pairs[k'.val] = tds.pairs[j.val] := by
            congr 1
          rw [hkd_eq]
          -- Derive `tds.getByKey kd.fst = some kd.snd` from membership.
          have hmem_list : tds.pairs[j.val] ∈ tds.pairs.toList :=
            Array.mem_toList_iff.mpr (Array.getElem_mem _)
          have hgetbykey : tds.getByKey tds.pairs[j.val].fst =
              some tds.pairs[j.val].snd :=
            IndexMap.getByKey_of_mem_pairs tds _ _ hmem_list
          refine ⟨?_, ?_⟩
          · -- Function-arm coverage.
            intro f hf_eq
            have hpe : f.params.isEmpty :=
              hfn_params tds.pairs[j.val].fst f (hf_eq ▸ hgetbykey)
            simp only [Fin.getElem_fin, hf_eq, hpe, ↓reduceIte]
            exact concretizeSeed_function_step_covers tds acc f
          · -- DataType-arm coverage.
            intro dt hd_eq
            have hpe : dt.params.isEmpty :=
              hdt_params tds.pairs[j.val].fst dt (hd_eq ▸ hgetbykey)
            simp only [Fin.getElem_fin, hd_eq, hpe, ↓reduceIte]
            exact concretizeSeed_dataType_step_covers acc dt
        · -- Past pair at k' < j: lift IH via step monotonicity.
          have hlt : k'.val < j.val := by omega
          exact (IH k' hlt).weaken _
            (fun q hq => concretizeSeed_step_subset tds tds.pairs[j.val] _ _ hq))
  -- Extract: for each `(key, d)` in tds.pairs, pairsCovered (concretizeSeed tds) (key, d).
  intro key d hgetbykey
  have hmem_list : (key, d) ∈ tds.pairs.toList :=
    IndexMap.mem_pairs_of_getByKey tds key d hgetbykey
  have hmem_arr : (key, d) ∈ tds.pairs := Array.mem_toList_iff.mp hmem_list
  obtain ⟨i, hi_lt, hi_eq⟩ := Array.mem_iff_getElem.mp hmem_arr
  have hcov : pairsCovered (tds.pairs.foldl _ {}) tds.pairs[i] :=
    h_motive ⟨i, hi_lt⟩ hi_lt
  rw [hi_eq] at hcov
  obtain ⟨h_fn, h_dt⟩ := hcov
  match d with
  | .function f =>
    show (∀ lt ∈ f.inputs, typOk lt.snd) ∧ typOk f.output
    exact h_fn f rfl
  | .dataType dt =>
    show ∀ c ∈ dt.constructors, ∀ ty ∈ c.argTypes, typOk ty
    exact h_dt dt rfl
  | .constructor dt c =>
    show ∀ ty ∈ c.argTypes, typOk ty
    intro ty hty
    -- Derive companion dataType's pairsCovered.
    obtain ⟨key', hkey', hc_in_dt⟩ := hctor_companion key dt c hgetbykey
    have hmem_list' : (key', .dataType dt) ∈ tds.pairs.toList :=
      IndexMap.mem_pairs_of_getByKey tds key' (.dataType dt) hkey'
    have hmem_arr' : (key', Typed.Declaration.dataType dt) ∈ tds.pairs :=
      Array.mem_toList_iff.mp hmem_list'
    obtain ⟨i', hi'_lt, hi'_eq⟩ := Array.mem_iff_getElem.mp hmem_arr'
    have hcov' := h_motive ⟨i', hi'_lt⟩ hi'_lt
    rw [hi'_eq] at hcov'
    obtain ⟨_, h_dt'⟩ := hcov'
    exact h_dt' dt rfl c hc_in_dt ty hty

/-- Empty initial state (with `pending := concretizeSeed tds`) satisfies
`AppsReached`, given FullyMono-derived params-empty facts +
ctor-companion presence (caller derives via L1 helpers).

Proof: the two `newDataTypes` / `newFunctions` clauses are vacuous (empty
arrays). The tds clause follows from `concretizeSeed_covers_tds_apps`
combined with the Or-injection: every `(g, args)` collected by the seed is
in `pending`, hence in `seen ∨ pending` (the right disjunct). -/
theorem DrainState.AppsReached.init (tds : Typed.Decls)
    (hfn_params : ∀ key f, tds.getByKey key = some (.function f) →
                           f.params.isEmpty)
    (hdt_params : ∀ key dt, tds.getByKey key = some (.dataType dt) →
                            dt.params.isEmpty)
    (hctor_companion : ∀ key dt c,
        tds.getByKey key = some (.constructor dt c) →
        ∃ key', tds.getByKey key' = some (.dataType dt) ∧
                c ∈ dt.constructors) :
    DrainState.AppsReached tds
      { pending := concretizeSeed tds, seen := {}, mono := {},
        newFunctions := #[], newDataTypes := #[] } := by
  have hseed := concretizeSeed_covers_tds_apps tds hfn_params hdt_params
                  hctor_companion
  -- Lift Or-into-Right via `Typ.AllAppsP` weakening.
  have hweaken : ∀ {t : Typ},
      Typ.AllAppsP (fun g args => (g, args) ∈ concretizeSeed tds) t →
      Typ.AllAppsP
        (fun g args => (g, args) ∈ ({} : Std.HashSet (Global × Array Typ)) ∨
                       (g, args) ∈ concretizeSeed tds) t := by
    intro t ht
    induction ht with
    | unit => exact .unit
    | field => exact .field
    | mvar n => exact .mvar n
    | ref g => exact .ref g
    | pointer _ ih => exact .pointer ih
    | tuple _ ih => exact .tuple ih
    | array _ ih => exact .array ih
    | function _ _ ihi iho => exact .function ihi iho
    | app _ hin ihsub => exact .app ihsub (Or.inr hin)
  refine ⟨?_, ?_, ?_⟩
  · intro key d hd
    have := hseed key d hd
    cases d with
    | function f =>
      simp only at this ⊢
      refine ⟨?_, ?_⟩
      · intro lt hlt; exact hweaken (this.1 lt hlt)
      · exact hweaken this.2
    | dataType dt =>
      simp only at this ⊢
      intro c hc ty hty
      exact hweaken (this c hc ty hty)
    | constructor dt c =>
      simp only at this ⊢
      intro ty hty
      exact hweaken (this ty hty)
  · intro dt hdt
    simp only [Array.not_mem_empty] at hdt
  · intro f hf
    simp only [Array.not_mem_empty] at hf

/-! ### `AppsReachedRel` — relativized invariant for iter-level preservation.

`concretizeDrainIter` zeroes `pending` before its foldlM, momentarily
breaking `AppsReached` (which requires `seen ∪ pending` coverage). The
relativized version `AppsReachedRel orig` adds `orig.pending` to the
coverage set; pending entries from before iter still count via `orig`. -/

/-- Relativized version of `AppsReached` that accepts a fixed `orig` state
whose `pending` augments the coverage set. `AppsReached st = AppsReachedRel st tds st`. -/
def DrainState.AppsReachedRel (st : DrainState) (tds : Typed.Decls)
    (orig : DrainState) : Prop :=
  let typOk : Typ → Prop := Typ.AllAppsP (fun g args =>
    (g, args) ∈ st.seen ∨ (g, args) ∈ st.pending ∨ (g, args) ∈ orig.pending)
  (∀ key d, tds.getByKey key = some d →
      match d with
      | .function f =>
          (∀ lt ∈ f.inputs, typOk lt.snd) ∧ typOk f.output
      | .dataType dt =>
          ∀ c ∈ dt.constructors, ∀ ty ∈ c.argTypes, typOk ty
      | .constructor _ c =>
          ∀ ty ∈ c.argTypes, typOk ty) ∧
  (∀ dt ∈ st.newDataTypes, ∀ c ∈ dt.constructors, ∀ ty ∈ c.argTypes, typOk ty) ∧
  (∀ f ∈ st.newFunctions,
    (∀ lt ∈ f.inputs, typOk lt.snd) ∧ typOk f.output)

/-- `AppsReached` is `AppsReachedRel` at orig = st. -/
theorem DrainState.AppsReached.toRel (tds : Typed.Decls) {st : DrainState}
    (h : st.AppsReached tds) : st.AppsReachedRel tds st := by
  obtain ⟨h_tds, h_dt, h_fn⟩ := h
  -- P → Q lift: (a ∨ b) → (a ∨ b ∨ c).
  have lift : ∀ {α β γ : Prop}, α ∨ β → α ∨ β ∨ γ :=
    fun ha => ha.elim Or.inl (fun hb => Or.inr (Or.inl hb))
  refine ⟨?_, ?_, ?_⟩
  · intro key d hd
    have := h_tds key d hd
    cases d with
    | function f =>
      simp only at this ⊢
      refine ⟨?_, ?_⟩
      · intro lt hlt
        exact (this.1 lt hlt).weaken (fun _ _ ha => lift ha)
      · exact this.2.weaken (fun _ _ ha => lift ha)
    | dataType dt =>
      simp only at this ⊢
      intro c hc ty hty
      exact (this c hc ty hty).weaken (fun _ _ ha => lift ha)
    | constructor dt c =>
      simp only at this ⊢
      intro ty hty
      exact (this ty hty).weaken (fun _ _ ha => lift ha)
  · intro dt hdt c hc ty hty
    exact (h_dt dt hdt c hc ty hty).weaken (fun _ _ ha => lift ha)
  · intro f hf
    obtain ⟨h_in, h_out⟩ := h_fn f hf
    refine ⟨?_, ?_⟩
    · intro lt hlt
      exact (h_in lt hlt).weaken (fun _ _ ha => lift ha)
    · exact h_out.weaken (fun _ _ ha => lift ha)

/-- If every entry in `orig.pending` is in `st.seen`, then `AppsReachedRel st tds orig`
collapses to plain `AppsReached st`. -/
theorem DrainState.AppsReachedRel.toAppsReached (tds : Typed.Decls)
    {orig st : DrainState}
    (hcollapse : ∀ q, q ∈ orig.pending → q ∈ st.seen)
    (h : st.AppsReachedRel tds orig) : st.AppsReached tds := by
  obtain ⟨h_tds, h_dt, h_fn⟩ := h
  -- Lift (a ∨ b ∨ c) where c → a, to (a ∨ b).
  have lift : ∀ {x : Global × Array Typ},
      ((x ∈ st.seen) ∨ (x ∈ st.pending) ∨ (x ∈ orig.pending)) →
      ((x ∈ st.seen) ∨ (x ∈ st.pending)) := by
    intro x ha
    rcases ha with hs | hp | ho
    · exact Or.inl hs
    · exact Or.inr hp
    · exact Or.inl (hcollapse _ ho)
  refine ⟨?_, ?_, ?_⟩
  · intro key d hd
    have := h_tds key d hd
    cases d with
    | function f =>
      simp only at this ⊢
      refine ⟨?_, ?_⟩
      · intro lt hlt; exact (this.1 lt hlt).weaken (fun _ _ ha => lift ha)
      · exact this.2.weaken (fun _ _ ha => lift ha)
    | dataType dt =>
      simp only at this ⊢
      intro c hc ty hty
      exact (this c hc ty hty).weaken (fun _ _ ha => lift ha)
    | constructor dt c =>
      simp only at this ⊢
      intro ty hty
      exact (this ty hty).weaken (fun _ _ ha => lift ha)
  · intro dt hdt c hc ty hty
    exact (h_dt dt hdt c hc ty hty).weaken (fun _ _ ha => lift ha)
  · intro f hf
    obtain ⟨h_in, h_out⟩ := h_fn f hf
    refine ⟨?_, ?_⟩
    · intro lt hlt; exact (h_in lt hlt).weaken (fun _ _ ha => lift ha)
    · exact h_out.weaken (fun _ _ ha => lift ha)

/-! ### `AppsReached` preservation chain.

Mirrors `SeenSubsetMono` chain. Key trick: prove preservation of relativized
`AppsReachedRel st tds orig` (with `orig` fixed); collapse to `AppsReached`
after fold consumes `orig.pending`. -/

/-- Entry-step preserves `AppsReachedRel`: state grows monotonically, new
newFn/newDt's apps land in pending'. -/
theorem concretizeDrainEntry_preserves_AppsReachedRel
    {tds : Typed.Decls} {orig state state' : DrainState}
    (hinv : state.AppsReachedRel tds orig) (entry : Global × Array Typ)
    (hstep : concretizeDrainEntry tds state entry = .ok state') :
    state'.AppsReachedRel tds orig := by
  unfold concretizeDrainEntry at hstep
  simp only [bind, Except.bind, pure, Except.pure] at hstep
  by_cases hseen : state.seen.contains (entry.1, entry.2)
  · simp [hseen] at hstep; rw [← hstep]; exact hinv
  · simp [hseen] at hstep
    -- Three cases: function arm success, dataType arm success, error throws.
    -- All success arms only GROW seen/pending/newFn/newDt; no removals.
    -- Coverage in old AppsReachedRel transfers via Or.weaken; new pushed
    -- newFn/newDt's apps covered by `collectInTyp`/`collectCalls` chain.
    obtain ⟨h_tds, h_dt, h_fn⟩ := hinv
    split at hstep
    · -- Function arm.
      rename_i f hf_get
      split at hstep
      · -- success: f.params.length = args.size
        simp only [Except.ok.injEq] at hstep
        rw [← hstep]
        -- New state:
        --   seen' = state.seen.insert entry
        --   pending' = collectCalls tds p3 newBody (⊇ p2 ⊇ p1 ⊇ state.pending)
        --   newFunctions' = state.newFunctions.push newFn
        --   newDataTypes' unchanged
        let newOutput := Typ.instantiate (mkParamSubst f.params entry.2) f.output
        let newInputs := f.inputs.map
          fun lt => (lt.1, Typ.instantiate (mkParamSubst f.params entry.2) lt.2)
        let newBody := substInTypedTerm (mkParamSubst f.params entry.2) f.body
        let p1 := collectInTyp state.pending newOutput
        let p2 := newInputs.foldl
          (fun s (lt : Local × Typ) => collectInTyp s lt.snd) p1
        let p3 := collectInTypedTerm p2 newBody
        let pending' := collectCalls tds p3 newBody
        -- Lift any AllAppsP (∈ p2) t through p3, pending'.
        have lift_p2 : ∀ {t : Typ},
            Typ.AllAppsP (fun g args => (g, args) ∈ p2) t →
            Typ.AllAppsP (fun g args => (g, args) ∈ pending') t := by
          intro t hp
          have hp_p3 := hp.weaken
            (fun _ _ ha => collectInTypedTerm_subset newBody _ _ ha)
          exact hp_p3.weaken (fun _ _ ha => collectCalls_subset tds newBody _ _ ha)
        -- Subset chain: state.pending ⊆ p1 ⊆ p2 ⊆ p3 ⊆ pending'.
        have hsub_pending : ∀ q, q ∈ state.pending → q ∈ pending' := by
          intro q hq
          have h_p1 : q ∈ p1 := collectInTyp_subset newOutput state.pending q hq
          have h_p2 : q ∈ p2 :=
            concretizeSeed_inputs_foldl_subset newInputs p1 q h_p1
          have h_p3 : q ∈ p3 := collectInTypedTerm_subset newBody p2 q h_p2
          exact collectCalls_subset tds newBody p3 q h_p3
        -- Lift weakening for "∈ state.seen ∨ state.pending ∨ orig.pending"
        -- to "∈ state'.seen ∨ pending' ∨ orig.pending".
        have growLift : ∀ {x : Global × Array Typ},
            ((x ∈ state.seen) ∨ (x ∈ state.pending) ∨ (x ∈ orig.pending)) →
            ((x ∈ state.seen.insert (entry.1, entry.2)) ∨
             (x ∈ pending') ∨ (x ∈ orig.pending)) := by
          intro x ha
          rcases ha with hs | hp | ho
          · exact Or.inl (Std.HashSet.mem_insert.mpr (Or.inr hs))
          · exact Or.inr (Or.inl (hsub_pending x hp))
          · exact Or.inr (Or.inr ho)
        refine ⟨?_, ?_, ?_⟩
        · intro key d hd
          have := h_tds key d hd
          cases d with
          | function f0 =>
            simp only at this ⊢
            refine ⟨?_, ?_⟩
            · intro lt hlt; exact (this.1 lt hlt).weaken (fun _ _ ha => growLift ha)
            · exact this.2.weaken (fun _ _ ha => growLift ha)
          | dataType dt0 =>
            simp only at this ⊢
            intro c hc ty hty
            exact (this c hc ty hty).weaken (fun _ _ ha => growLift ha)
          | constructor dt0 c =>
            simp only at this ⊢
            intro ty hty
            exact (this ty hty).weaken (fun _ _ ha => growLift ha)
        · intro dt hdt c hc ty hty
          exact (h_dt dt hdt c hc ty hty).weaken (fun _ _ ha => growLift ha)
        · intro f' hf'
          simp only [Array.mem_push] at hf'
          rcases hf' with hold | hnew
          · -- Old function: lift via growLift.
            obtain ⟨h_in, h_out⟩ := h_fn f' hold
            refine ⟨?_, ?_⟩
            · intro lt hlt; exact (h_in lt hlt).weaken (fun _ _ ha => growLift ha)
            · exact h_out.weaken (fun _ _ ha => growLift ha)
          · -- New function (just pushed): apps in its types are in pending'.
            subst hnew
            simp only
            -- Coverage of newOutput: via collectInTyp_collects_apps + lift through p2 / pending'.
            have hcov_out : Typ.AllAppsP
                (fun g args => (g, args) ∈ p1) newOutput :=
              collectInTyp_collects_apps newOutput state.pending
            have hcov_p2_out : Typ.AllAppsP
                (fun g args => (g, args) ∈ p2) newOutput :=
              AllAppsP_inputs_foldl_mono newOutput newInputs p1 hcov_out
            have hcov_pending'_out : Typ.AllAppsP
                (fun g args => (g, args) ∈ pending') newOutput :=
              lift_p2 hcov_p2_out
            -- For each input lt: cover via AllAppsP_inputs_foldl_covers.
            refine ⟨?_, ?_⟩
            · intro lt hlt
              have hcov_p2_lt : Typ.AllAppsP
                  (fun g args => (g, args) ∈ p2) lt.snd :=
                AllAppsP_inputs_foldl_covers newInputs p1 lt hlt
              exact (lift_p2 hcov_p2_lt).weaken
                (fun _ _ ha => Or.inr (Or.inl ha))
            · exact hcov_pending'_out.weaken
                (fun _ _ ha => Or.inr (Or.inl ha))
      · cases hstep
    · -- DataType arm.
      rename_i dt hdt_get
      split at hstep
      · simp only [Except.ok.injEq] at hstep
        rw [← hstep]
        let subst := mkParamSubst dt.params entry.2
        let newCtors : List Constructor := dt.constructors.map (fun c =>
          ({ c with argTypes := c.argTypes.map (Typ.instantiate subst) }))
        let pending' := newCtors.foldl
          (fun s (c : Constructor) => c.argTypes.foldl collectInTyp s)
          state.pending
        have hsub_pending : ∀ q, q ∈ state.pending → q ∈ pending' := by
          intro q hq
          exact concretizeSeed_dt_ctors_foldl_subset newCtors state.pending q hq
        have growLift : ∀ {x : Global × Array Typ},
            ((x ∈ state.seen) ∨ (x ∈ state.pending) ∨ (x ∈ orig.pending)) →
            ((x ∈ state.seen.insert (entry.1, entry.2)) ∨
             (x ∈ pending') ∨ (x ∈ orig.pending)) := by
          intro x ha
          rcases ha with hs | hp | ho
          · exact Or.inl (Std.HashSet.mem_insert.mpr (Or.inr hs))
          · exact Or.inr (Or.inl (hsub_pending x hp))
          · exact Or.inr (Or.inr ho)
        refine ⟨?_, ?_, ?_⟩
        · intro key d hd
          have := h_tds key d hd
          cases d with
          | function f0 =>
            simp only at this ⊢
            refine ⟨?_, ?_⟩
            · intro lt hlt; exact (this.1 lt hlt).weaken (fun _ _ ha => growLift ha)
            · exact this.2.weaken (fun _ _ ha => growLift ha)
          | dataType dt0 =>
            simp only at this ⊢
            intro c hc ty hty
            exact (this c hc ty hty).weaken (fun _ _ ha => growLift ha)
          | constructor dt0 c =>
            simp only at this ⊢
            intro ty hty
            exact (this ty hty).weaken (fun _ _ ha => growLift ha)
        · intro dt' hdt'
          simp only [Array.mem_push] at hdt'
          rcases hdt' with hold | hnew
          · intro c hc ty hty
            exact (h_dt dt' hold c hc ty hty).weaken
              (fun _ _ ha => growLift ha)
          · -- New datatype: ctor argTypes' apps in pending'.
            subst hnew
            simp only
            intro c hc ty hty
            -- c ∈ newCtors (the just-built map result).
            have hcov : Typ.AllAppsP
                (fun g args => (g, args) ∈ pending') ty :=
              AllAppsP_dt_ctors_foldl_covers newCtors state.pending c hc ty hty
            exact hcov.weaken (fun _ _ ha => Or.inr (Or.inl ha))
        · intro f' hf'
          obtain ⟨h_in, h_out⟩ := h_fn f' hf'
          refine ⟨?_, ?_⟩
          · intro lt hlt; exact (h_in lt hlt).weaken (fun _ _ ha => growLift ha)
          · exact h_out.weaken (fun _ _ ha => growLift ha)
      · cases hstep
    · cases hstep

/-- List-foldlM of `concretizeDrainEntry` preserves `AppsReachedRel`. -/
theorem concretizeDrainEntry_list_foldlM_preserves_AppsReachedRel
    {tds : Typed.Decls} {orig : DrainState}
    (L : List (Global × Array Typ))
    (state0 state' : DrainState)
    (hinv0 : state0.AppsReachedRel tds orig)
    (hstep : L.foldlM (concretizeDrainEntry tds) state0 = .ok state') :
    state'.AppsReachedRel tds orig := by
  induction L generalizing state0 with
  | nil =>
    simp only [List.foldlM, pure, Except.pure, Except.ok.injEq] at hstep
    rw [← hstep]; exact hinv0
  | cons hd tl ih =>
    simp only [List.foldlM, bind, Except.bind] at hstep
    split at hstep
    · cases hstep
    · rename_i s'' hs''
      have hinv1 : s''.AppsReachedRel tds orig :=
        concretizeDrainEntry_preserves_AppsReachedRel hinv0 hd hs''
      exact ih s'' hinv1 hstep

/-- After the iter's foldlM, every entry in the original `pending` (= the batch)
ended up in `state'.seen`. Used to collapse `AppsReachedRel` back to `AppsReached`. -/
theorem concretizeDrainEntry_inserts_into_seen
    {tds : Typed.Decls} {state state' : DrainState}
    (entry : Global × Array Typ)
    (hstep : concretizeDrainEntry tds state entry = .ok state') :
    (entry.1, entry.2) ∈ state'.seen ∧
    (∀ q, q ∈ state.seen → q ∈ state'.seen) := by
  unfold concretizeDrainEntry at hstep
  simp only [bind, Except.bind, pure, Except.pure] at hstep
  by_cases hseen : state.seen.contains (entry.1, entry.2)
  · simp [hseen] at hstep
    rw [← hstep]
    refine ⟨?_, fun q hq => hq⟩
    exact Std.HashSet.contains_iff_mem.mp hseen
  · simp [hseen] at hstep
    split at hstep
    · rename_i f hf_get
      split at hstep
      · simp only [Except.ok.injEq] at hstep
        rw [← hstep]
        refine ⟨?_, ?_⟩
        · simp only; rw [Std.HashSet.mem_insert]; exact Or.inl BEq.rfl
        · intro q hq; rw [Std.HashSet.mem_insert]; exact Or.inr hq
      · cases hstep
    · rename_i dt hdt_get
      split at hstep
      · simp only [Except.ok.injEq] at hstep
        rw [← hstep]
        refine ⟨?_, ?_⟩
        · simp only; rw [Std.HashSet.mem_insert]; exact Or.inl BEq.rfl
        · intro q hq; rw [Std.HashSet.mem_insert]; exact Or.inr hq
      · cases hstep
    · cases hstep

/-- After list-foldlM, every batch entry is in state'.seen, and old seen survives. -/
theorem concretizeDrainEntry_list_foldlM_consumes_batch
    {tds : Typed.Decls}
    (L : List (Global × Array Typ))
    (state0 state' : DrainState)
    (hstep : L.foldlM (concretizeDrainEntry tds) state0 = .ok state') :
    (∀ q ∈ L, q ∈ state'.seen) ∧ (∀ q, q ∈ state0.seen → q ∈ state'.seen) := by
  induction L generalizing state0 with
  | nil =>
    simp only [List.foldlM, pure, Except.pure, Except.ok.injEq] at hstep
    refine ⟨?_, ?_⟩
    · intro q hq; cases hq
    · intro q hq; rw [← hstep]; exact hq
  | cons hd tl ih =>
    simp only [List.foldlM, bind, Except.bind] at hstep
    split at hstep
    · cases hstep
    · rename_i s'' hs''
      obtain ⟨hd_in_s'', hold_in_s''⟩ :=
        concretizeDrainEntry_inserts_into_seen hd hs''
      obtain ⟨h_tl_in_s', hs''_in_s'⟩ := ih s'' hstep
      refine ⟨?_, ?_⟩
      · intro q hq
        rcases List.mem_cons.mp hq with heq | hin
        · subst heq; exact hs''_in_s' _ hd_in_s''
        · exact h_tl_in_s' q hin
      · intro q hq
        exact hs''_in_s' q (hold_in_s'' q hq)

/-- Iter preserves `AppsReached`: relativize, fold, collapse. -/
theorem concretizeDrainIter_preserves_AppsReached
    {tds : Typed.Decls} {state state' : DrainState}
    (hinv : state.AppsReached tds)
    (hstep : concretizeDrainIter tds state = .ok state') :
    state'.AppsReached tds := by
  unfold concretizeDrainIter at hstep
  rw [← Array.foldlM_toList] at hstep
  -- state0 = { state with pending := ∅ }.
  let state0 : DrainState := { state with pending := ∅ }
  -- AppsReachedRel state0 tds state holds: coverage = state0.seen ∪ ∅ ∪ state.pending
  --  = state.seen ∪ state.pending = AppsReached state's coverage.
  have hinv_rel : state0.AppsReachedRel tds state := by
    have hinit : state.AppsReachedRel tds state := DrainState.AppsReached.toRel tds hinv
    -- state0 differs from state only in pending (= ∅). So AppsReachedRel state0 tds state:
    -- coverage = state0.seen ∪ state0.pending ∪ state.pending = state.seen ∪ ∅ ∪ state.pending.
    -- Use lift to reshape: state0.pending = ∅ contributes nothing.
    obtain ⟨h_tds, h_dt, h_fn⟩ := hinit
    have lift : ∀ {x : Global × Array Typ},
        ((x ∈ state.seen) ∨ (x ∈ state.pending) ∨ (x ∈ state.pending)) →
        ((x ∈ state0.seen) ∨ (x ∈ state0.pending) ∨ (x ∈ state.pending)) := by
      intro x ha
      rcases ha with hs | hp | ho
      · exact Or.inl hs
      · exact Or.inr (Or.inr hp)
      · exact Or.inr (Or.inr ho)
    refine ⟨?_, ?_, ?_⟩
    · intro key d hd
      have := h_tds key d hd
      cases d with
      | function f =>
        simp only at this ⊢
        refine ⟨?_, ?_⟩
        · intro lt hlt; exact (this.1 lt hlt).weaken (fun _ _ ha => lift ha)
        · exact this.2.weaken (fun _ _ ha => lift ha)
      | dataType dt =>
        simp only at this ⊢
        intro c hc ty hty
        exact (this c hc ty hty).weaken (fun _ _ ha => lift ha)
      | constructor dt c =>
        simp only at this ⊢
        intro ty hty
        exact (this ty hty).weaken (fun _ _ ha => lift ha)
    · intro dt hdt c hc ty hty
      exact (h_dt dt hdt c hc ty hty).weaken (fun _ _ ha => lift ha)
    · intro f hf
      obtain ⟨h_in, h_out⟩ := h_fn f hf
      refine ⟨?_, ?_⟩
      · intro lt hlt; exact (h_in lt hlt).weaken (fun _ _ ha => lift ha)
      · exact h_out.weaken (fun _ _ ha => lift ha)
  -- After foldlM, AppsReachedRel state' tds state.
  have hinv_rel' : state'.AppsReachedRel tds state :=
    concretizeDrainEntry_list_foldlM_preserves_AppsReachedRel
      state.pending.toArray.toList state0 state' hinv_rel hstep
  -- And state.pending ⊆ state'.seen (batch consumed).
  have ⟨hbatch_in_seen, _⟩ :=
    concretizeDrainEntry_list_foldlM_consumes_batch
      state.pending.toArray.toList state0 state' hstep
  -- Collapse.
  apply DrainState.AppsReachedRel.toAppsReached tds
  · intro q hq
    apply hbatch_in_seen
    -- q ∈ state.pending → q ∈ state.pending.toArray.toList.
    rw [Array.mem_toList_iff, Std.HashSet.mem_toArray]
    exact hq
  · exact hinv_rel'

/-- Drain preserves `AppsReached`. Mirrors `concretize_drain_preserves_SeenSubsetMono`. -/
theorem concretize_drain_preserves_AppsReached
    {tds : Typed.Decls} (fuel : Nat) (init : DrainState)
    (hinv : init.AppsReached tds)
    {drained : DrainState}
    (hdrain : concretizeDrain tds fuel init = .ok drained) :
    drained.AppsReached tds := by
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
        have hinv' : state'.AppsReached tds :=
          concretizeDrainIter_preserves_AppsReached hinv hstate'
        exact ih state' hinv' hdrain

/-- After one iter step, the original `state.pending` is entirely consumed
into `state'.seen`. Combined with monotonicity, every entry in
`state.pending` ends up in any later state's `seen`. -/
theorem concretizeDrainIter_pending_in_seen
    {tds : Typed.Decls} {state state' : DrainState}
    (hstep : concretizeDrainIter tds state = .ok state') :
    (∀ q, q ∈ state.pending → q ∈ state'.seen) ∧
    (∀ q, q ∈ state.seen → q ∈ state'.seen) := by
  unfold concretizeDrainIter at hstep
  rw [← Array.foldlM_toList] at hstep
  let state0 : DrainState := { state with pending := ∅ }
  -- Apply consumes_batch: every batch entry (= state.pending) lands in state'.seen,
  -- and state0.seen = state.seen survives.
  have ⟨hbatch, hold⟩ :=
    concretizeDrainEntry_list_foldlM_consumes_batch
      state.pending.toArray.toList state0 state' hstep
  refine ⟨?_, ?_⟩
  · intro q hq
    apply hbatch
    rw [Array.mem_toList_iff, Std.HashSet.mem_toArray]
    exact hq
  · -- state0.seen = state.seen.
    intro q hq
    exact hold q hq

/-- Drain preserves seen-monotonicity: every entry in init.seen survives in
drained.seen. Helper for `concretize_drain_init_pending_in_seen`. -/
theorem concretize_drain_seen_subset
    {tds : Typed.Decls} (fuel : Nat) {init drained : DrainState}
    (hdrain : concretizeDrain tds fuel init = .ok drained) :
    ∀ q, q ∈ init.seen → q ∈ drained.seen := by
  induction fuel generalizing init with
  | zero =>
    unfold concretizeDrain at hdrain
    by_cases hpen : init.pending.isEmpty
    · simp only [hpen, if_true, pure, Except.pure, Except.ok.injEq] at hdrain
      intro q hq; rw [← hdrain]; exact hq
    · simp [hpen] at hdrain
  | succ n ih =>
    unfold concretizeDrain at hdrain
    by_cases hpen : init.pending.isEmpty
    · simp only [hpen, if_true, pure, Except.pure, Except.ok.injEq] at hdrain
      intro q hq; rw [← hdrain]; exact hq
    · simp only [hpen, if_false, Bool.false_eq_true] at hdrain
      simp only [bind, Except.bind] at hdrain
      split at hdrain
      · cases hdrain
      · rename_i state' hstate'
        intro q hq
        have ⟨_, hold⟩ := concretizeDrainIter_pending_in_seen hstate'
        exact ih hdrain q (hold q hq)

/-- Drain (over fuel) preserves: every entry in the initial state's pending
ends up in the drained state's seen. Iter-by-iter: each iter consumes its
state's pending into seen; later iters only grow seen. -/
theorem concretize_drain_init_pending_in_seen
    {tds : Typed.Decls} (fuel : Nat) (init : DrainState) {drained : DrainState}
    (hdrain : concretizeDrain tds fuel init = .ok drained) :
    ∀ q, q ∈ init.pending → q ∈ drained.seen := by
  induction fuel generalizing init with
  | zero =>
    unfold concretizeDrain at hdrain
    by_cases hpen : init.pending.isEmpty
    · simp only [hpen, if_true, pure, Except.pure, Except.ok.injEq] at hdrain
      intro q hq
      have hcontains : init.pending.contains q := Std.HashSet.contains_iff_mem.mpr hq
      rw [Std.HashSet.isEmpty_eq_false_iff_exists_contains_eq_true.mpr ⟨q, hcontains⟩] at hpen
      cases hpen
    · simp [hpen] at hdrain
  | succ n ih =>
    unfold concretizeDrain at hdrain
    by_cases hpen : init.pending.isEmpty
    · simp only [hpen, if_true, pure, Except.pure, Except.ok.injEq] at hdrain
      intro q hq
      have hcontains : init.pending.contains q := Std.HashSet.contains_iff_mem.mpr hq
      rw [Std.HashSet.isEmpty_eq_false_iff_exists_contains_eq_true.mpr ⟨q, hcontains⟩] at hpen
      cases hpen
    · simp only [hpen, if_false, Bool.false_eq_true] at hdrain
      simp only [bind, Except.bind] at hdrain
      split at hdrain
      · cases hdrain
      · rename_i state' hstate'
        intro q hq
        have ⟨hpen_seen, _⟩ := concretizeDrainIter_pending_in_seen hstate'
        have hq_state' : q ∈ state'.seen := hpen_seen q hq
        exact concretize_drain_seen_subset n hdrain q hq_state'

/-! ### `NewDtFnInSeen` preservation chain. -/

theorem concretizeDrainEntry_preserves_NewDtFnInSeen
    {decls : Typed.Decls} {state state' : DrainState}
    (hinv : state.NewDtFnInSeen) (entry : Global × Array Typ)
    (hstep : concretizeDrainEntry decls state entry = .ok state') :
    state'.NewDtFnInSeen := by
  unfold concretizeDrainEntry at hstep
  simp only [bind, Except.bind, pure, Except.pure] at hstep
  by_cases hseen : state.seen.contains (entry.1, entry.2)
  · simp [hseen] at hstep; rw [← hstep]; exact hinv
  · simp [hseen] at hstep
    obtain ⟨h_fn, h_dt⟩ := hinv
    split at hstep
    · -- Function arm.
      rename_i f hf_get
      by_cases hsz : f.params.length = entry.2.size
      · simp [hsz] at hstep
        rw [← hstep]
        refine ⟨?_, ?_⟩
        · intro f' hf'mem
          rcases Array.mem_push.mp hf'mem with hin | heq
          · obtain ⟨g, args, hname, hin_seen⟩ := h_fn f' hin
            refine ⟨g, args, hname, ?_⟩
            rw [Std.HashSet.mem_insert]; exact Or.inr hin_seen
          · subst heq
            refine ⟨entry.1, entry.2, rfl, ?_⟩
            simp only
            rw [Std.HashSet.mem_insert]; exact Or.inl BEq.rfl
        · intro dt hdt
          obtain ⟨g, args, hname, hin_seen⟩ := h_dt dt hdt
          refine ⟨g, args, hname, ?_⟩
          rw [Std.HashSet.mem_insert]; exact Or.inr hin_seen
      · simp [hsz] at hstep
    · -- DataType arm.
      rename_i dt hdt_get
      by_cases hsz : dt.params.length = entry.2.size
      · simp [hsz] at hstep
        rw [← hstep]
        refine ⟨?_, ?_⟩
        · intro f hf
          obtain ⟨g, args, hname, hin_seen⟩ := h_fn f hf
          refine ⟨g, args, hname, ?_⟩
          rw [Std.HashSet.mem_insert]; exact Or.inr hin_seen
        · intro dt' hdt'mem
          rcases Array.mem_push.mp hdt'mem with hin | heq
          · obtain ⟨g, args, hname, hin_seen⟩ := h_dt dt' hin
            refine ⟨g, args, hname, ?_⟩
            rw [Std.HashSet.mem_insert]; exact Or.inr hin_seen
          · subst heq
            refine ⟨entry.1, entry.2, rfl, ?_⟩
            simp only
            rw [Std.HashSet.mem_insert]; exact Or.inl BEq.rfl
      · simp [hsz] at hstep
    · cases hstep

theorem concretizeDrainEntry_list_foldlM_preserves_NewDtFnInSeen
    {decls : Typed.Decls}
    (L : List (Global × Array Typ))
    (state0 state' : DrainState)
    (hinv0 : state0.NewDtFnInSeen)
    (hstep : L.foldlM (concretizeDrainEntry decls) state0 = .ok state') :
    state'.NewDtFnInSeen := by
  induction L generalizing state0 with
  | nil =>
    simp only [List.foldlM, pure, Except.pure, Except.ok.injEq] at hstep
    rw [← hstep]; exact hinv0
  | cons hd tl ih =>
    simp only [List.foldlM, bind, Except.bind] at hstep
    split at hstep
    · cases hstep
    · rename_i s'' hs''
      have hinv1 : s''.NewDtFnInSeen :=
        concretizeDrainEntry_preserves_NewDtFnInSeen hinv0 hd hs''
      exact ih s'' hinv1 hstep

theorem concretizeDrainIter_preserves_NewDtFnInSeen
    {decls : Typed.Decls} {state state' : DrainState}
    (hinv : state.NewDtFnInSeen)
    (hstep : concretizeDrainIter decls state = .ok state') :
    state'.NewDtFnInSeen := by
  unfold concretizeDrainIter at hstep
  rw [← Array.foldlM_toList] at hstep
  let state0 : DrainState := { state with pending := ∅ }
  have hinv0 : state0.NewDtFnInSeen := hinv
  exact concretizeDrainEntry_list_foldlM_preserves_NewDtFnInSeen
    state.pending.toArray.toList state0 state' hinv0 hstep

theorem concretize_drain_preserves_NewDtFnInSeen
    {decls : Typed.Decls} (fuel : Nat) (init : DrainState)
    (hinv : init.NewDtFnInSeen)
    {drained : DrainState}
    (hdrain : concretizeDrain decls fuel init = .ok drained) :
    drained.NewDtFnInSeen := by
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
        have hinv' : state'.NewDtFnInSeen :=
          concretizeDrainIter_preserves_NewDtFnInSeen hinv hstate'
        exact ih state' hinv' hdrain

/-- Drain success implies `drained.pending.isEmpty`. -/
theorem concretize_drain_succeeds_pending_empty
    {tds : Typed.Decls} (fuel : Nat) (init : DrainState) {drained : DrainState}
    (hdrain : concretizeDrain tds fuel init = .ok drained) :
    drained.pending.isEmpty := by
  induction fuel generalizing init with
  | zero =>
    unfold concretizeDrain at hdrain
    by_cases hpen : init.pending.isEmpty
    · simp only [hpen, if_true, pure, Except.pure, Except.ok.injEq] at hdrain
      rw [← hdrain]; exact hpen
    · simp [hpen] at hdrain
  | succ n ih =>
    unfold concretizeDrain at hdrain
    by_cases hpen : init.pending.isEmpty
    · simp only [hpen, if_true, pure, Except.pure, Except.ok.injEq] at hdrain
      rw [← hdrain]; exact hpen
    · simp only [hpen, if_false, Bool.false_eq_true] at hdrain
      simp only [bind, Except.bind] at hdrain
      split at hdrain
      · cases hdrain
      · rename_i state' _
        exact ih state' hdrain

end Aiur

end -- @[expose] section
end
