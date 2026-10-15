import Ix.CompileM

/-! # Running the compiler monad, for proofs

`rawRun` runs a `CompileM` action from a block state and returns its outcome
together with the final state, which the monad keeps on errors too.
`Preserves p action` says that the action leaves the projection `p` of the
block state unchanged on every run, failing ones included. These are the
frame facts of the universe proofs; they hold for the compiler's actual
functions, not copies.

The run equations of every `CompileM` primitive, the bind inversions
(`bind_ok`, `bind_success`), the frame combinators for maps and loops, and
`Triple`, a success-only Hoare triple with one set of combinators, are the
one run layer the reading proofs share, so that each invariant over
`CompileM` is an instance of these instead of a copy of them. -/

namespace Ix.CompileCert

open Ix.CompileM

/-- One run of a compiler action: its outcome and the final block state. -/
def rawRun (action : CompileM α) (context : CompileEnv × BlockEnv) (state : BlockState) :
    Except CompileError α × BlockState := (action context).run state

theorem rawRun_bind (action : CompileM α) (next : α → CompileM β)
    (context : CompileEnv × BlockEnv) (state : BlockState) :
    rawRun (action >>= next) context state =
      match rawRun action context state with
      | (.ok value, after) => rawRun (next value) context after
      | (.error error, after) => (.error error, after) := by
  rcases result : (action context).run state with ⟨outcome, after⟩
  change action context state = (outcome, after) at result
  cases outcome <;>
    simp [rawRun, ExceptT.run, ExceptT.mk, bind, ReaderT.bind, ExceptT.bind, StateT.bind,
      ExceptT.bindCont, pure, StateT.pure, result]

theorem rawRun_pure (value : α) (context : CompileEnv × BlockEnv) (state : BlockState) :
    rawRun (pure value) context state = (.ok value, state) := rfl

theorem rawRun_read (context : CompileEnv × BlockEnv) (state : BlockState) :
    rawRun getCompileEnv context state = (.ok context.1, state) := rfl

theorem rawRun_readBlock (context : CompileEnv × BlockEnv) (state : BlockState) :
    rawRun getBlockEnv context state = (.ok context.2, state) := rfl

theorem rawRun_get (context : CompileEnv × BlockEnv) (state : BlockState) :
    rawRun getBlockState context state = (.ok state, state) := rfl

theorem rawRun_modify (update : BlockState → BlockState)
    (context : CompileEnv × BlockEnv) (state : BlockState) :
    rawRun (modifyBlockState update) context state = (.ok (), update state) := rfl

/-- The action keeps the projection `projection` of the block state, on
every run. -/
def Preserves (projection : BlockState → α) (action : CompileM β) : Prop :=
  ∀ context before, projection (rawRun action context before).2 = projection before

theorem Preserves.pure (projection : BlockState → α) (value : β) : Preserves projection (pure value) := by
  intro context before; rfl

theorem Preserves.throw (projection : BlockState → α) (error : CompileError) :
    Preserves projection (throw error : CompileM β) := by intro context before; rfl

theorem Preserves.get (projection : BlockState → α) : Preserves projection getBlockState := by
  intro context before; rfl

theorem Preserves.read (projection : BlockState → α) : Preserves projection getBlockEnv := by
  intro context before; rfl

theorem Preserves.modify (projection : BlockState → α) (update : BlockState → BlockState)
    (unchanged : ∀ before, projection (update before) = projection before) :
    Preserves projection (modifyBlockState update) := by intro context before; exact unchanged before

theorem Preserves.bind {projection : BlockState → α} {action : CompileM β} {next : β → CompileM γ}
    (first : Preserves projection action) (later : ∀ value, Preserves projection (next value)) :
    Preserves projection (action >>= next) := by
  intro context before
  rw [rawRun_bind]
  have prior := first context before
  cases ran : rawRun action context before with
  | mk outcome after =>
    rw [ran] at prior
    cases outcome with
    | error error => exact prior
    | ok value => exact (later value context after).trans prior

/-! ## More run equations

The remaining primitives of `CompileM`, the pure-state helper
`applyBlockState`, and `CompileM.run` in terms of `rawRun`. -/

theorem rawRun_throw (error : CompileError) (context : CompileEnv × BlockEnv) (state : BlockState) :
    rawRun (throw error : CompileM α) context state = (.error error, state) := rfl

theorem rawRun_modifyGet (update : BlockState → α × BlockState)
    (context : CompileEnv × BlockEnv) (state : BlockState) :
    rawRun (modifyGetBlockState update) context state = (.ok (update state).1, (update state).2) := rfl

theorem rawRun_withBlockEnv (update : BlockEnv → BlockEnv) (action : CompileM α)
    (context : CompileEnv × BlockEnv) (state : BlockState) :
    rawRun (withBlockEnv update action) context state = rawRun action (context.1, update context.2) state :=
  rfl

theorem rawRun_applyBlockState (result : Except CompileError BlockState)
    (context : CompileEnv × BlockEnv) (state : BlockState) :
    rawRun (applyBlockState result) context state = match result with
      | .error error => (.error error, state)
      | .ok after => (.ok (), after) := by cases result <;> rfl

theorem run_eq_rawRun (action : CompileM α) (cenv : CompileEnv) (benv : BlockEnv) (state : BlockState) :
    CompileM.run cenv benv state action =
      match rawRun action (cenv, benv) state with
      | (.ok value, after) => .ok (value, after)
      | (.error error, _) => .error error := rfl

theorem run_success {action : CompileM α} {cenv : CompileEnv} {benv : BlockEnv}
    {before after : BlockState} {value : α}
    (success : CompileM.run cenv benv before action = .ok (value, after)) :
    rawRun action (cenv, benv) before = (.ok value, after) := by
  rw [run_eq_rawRun] at success
  cases ran : rawRun action (cenv, benv) before with
  | mk outcome final =>
    rw [ran] at success
    cases outcome <;> try contradiction
    cases Except.ok.inj success
    rfl

/-- A successful bind ran both halves successfully. -/
theorem bind_ok {action : CompileM α} {next : α → CompileM β}
    {context : CompileEnv × BlockEnv} {before : BlockState} {value : β} {after : BlockState}
    (success : rawRun (action >>= next) context before = (.ok value, after)) :
    ∃ first middle, rawRun action context before = (.ok first, middle) ∧
      rawRun (next first) context middle = (.ok value, after) := by
  rw [rawRun_bind] at success
  cases ran : rawRun action context before with
  | mk outcome middle =>
    rw [ran] at success
    cases outcome with
    | error error => cases success
    | ok first => exact ⟨first, middle, rfl, success⟩

/-- `bind_ok` for the outcome alone. -/
theorem bind_success {action : CompileM α} {next : α → CompileM β}
    {context : CompileEnv × BlockEnv} {before : BlockState} {value : β}
    (success : (rawRun (action >>= next) context before).1 = .ok value) :
    ∃ first middle, rawRun action context before = (.ok first, middle) ∧
      (rawRun (next first) context middle).1 = .ok value := by
  rw [rawRun_bind] at success
  cases ran : rawRun action context before with
  | mk outcome middle =>
    rw [ran] at success
    cases outcome with
    | error error => cases success
    | ok first => exact ⟨first, middle, rfl, success⟩

/-! ## More frame combinators -/

theorem Preserves.readCompile (projection : BlockState → α) : Preserves projection getCompileEnv := by
  intro context before; rfl

theorem Preserves.modifyGet (projection : BlockState → α) (update : BlockState → β × BlockState)
    (unchanged : ∀ before, projection (update before).2 = projection before) :
    Preserves projection (modifyGetBlockState update) := by
  intro context before; exact unchanged before

theorem Preserves.map {projection : BlockState → α} {action : CompileM β}
    (framed : Preserves projection action) (f : β → γ) : Preserves projection (f <$> action) :=
  Preserves.bind framed (fun _ => Preserves.pure _ _)

theorem Preserves.withBlockEnv {projection : BlockState → α} {action : CompileM β}
    (framed : Preserves projection action) (update : BlockEnv → BlockEnv) :
    Preserves projection (withBlockEnv update action) := by
  intro context before
  rw [rawRun_withBlockEnv]
  exact framed _ before

theorem Preserves.mapM_list {projection : BlockState → α} (items : List β) (action : β → CompileM γ)
    (keeps : ∀ item ∈ items, Preserves projection (action item)) :
    Preserves projection (items.mapM action) := by
  induction items with
  | nil => exact Preserves.pure _ []
  | cons item rest ih =>
    rw [List.mapM_cons]
    apply Preserves.bind (keeps item (by simp))
    intro _
    apply Preserves.bind (ih (fun item mem => keeps item (List.mem_cons_of_mem _ mem)))
    intro _
    exact Preserves.pure _ _

theorem Preserves.mapM_array {projection : BlockState → α} (items : Array β) (action : β → CompileM γ)
    (keeps : ∀ item ∈ items, Preserves projection (action item)) :
    Preserves projection (items.mapM action) := by
  rw [Array.mapM_eq_mapM_toList]
  exact (Preserves.mapM_list _ action (fun item mem => keeps item (by simpa using mem))).map _

theorem Preserves.forIn'_list {projection : BlockState → α} (items : List β) (initial : γ)
    (body : (item : β) → item ∈ items → γ → CompileM (ForInStep γ))
    (keeps : ∀ item mem acc, Preserves projection (body item mem acc)) :
    Preserves projection (forIn' items initial body) := by
  induction items generalizing initial with
  | nil => exact Preserves.pure _ initial
  | cons item rest ih =>
    rw [List.forIn'_cons]
    apply Preserves.bind (keeps item (by simp) initial)
    intro result
    cases result with
    | done value => exact Preserves.pure _ value
    | yield value => exact ih value _ (fun item mem acc => keeps item _ acc)

theorem Preserves.forIn'_array {projection : BlockState → α} (items : Array β) (initial : γ)
    (body : (item : β) → item ∈ items → γ → CompileM (ForInStep γ))
    (keeps : ∀ item mem acc, Preserves projection (body item mem acc)) :
    Preserves projection (forIn' items initial body) := by
  have listFrame := Preserves.forIn'_list items.toList initial
    (fun item mem acc => body item (Array.mem_toList_iff.mp mem) acc)
    (fun item mem acc => keeps item _ acc)
  simpa only [Array.forIn'_toList] using listFrame

theorem Preserves.forIn_list {projection : BlockState → α} (items : List β) (initial : γ)
    (body : β → γ → CompileM (ForInStep γ)) (keeps : ∀ item acc, Preserves projection (body item acc)) :
    Preserves projection (forIn items initial body) := by
  induction items generalizing initial with
  | nil => exact Preserves.pure _ initial
  | cons item rest ih =>
    rw [List.forIn_cons]
    apply Preserves.bind (keeps item initial)
    intro result
    cases result with
    | done value => exact Preserves.pure _ value
    | yield value => exact ih value

theorem Preserves.forIn_array {projection : BlockState → α} (items : Array β) (initial : γ)
    (body : β → γ → CompileM (ForInStep γ)) (keeps : ∀ item acc, Preserves projection (body item acc)) :
    Preserves projection (forIn items initial body) := by
  rw [← Array.forIn_toList]
  exact Preserves.forIn_list items.toList initial body keeps

/-- A projection the action keeps is kept by a successful run in particular. -/
theorem Preserves.of_ok {projection : BlockState → α} {action : CompileM β}
    (framed : Preserves projection action) {context : CompileEnv × BlockEnv}
    {before after : BlockState} {value : β}
    (ran : rawRun action context before = (.ok value, after)) : projection after = projection before := by
  have kept := framed context before
  rw [ran] at kept
  exact kept

/-! ## Success-only triples

`Triple context pre action post`: every successful run of `action` under
`context` from a state satisfying `pre` returns a value and a state
satisfying `post`. Failing runs are unconstrained. It is the generic shape
of the per-proof "on success, the state keeps an invariant and the value
means something" predicates (R07-03), with one set of combinators. -/

def Triple (context : CompileEnv × BlockEnv) (pre : BlockState → Prop) (action : CompileM α)
    (post : α → BlockState → Prop) : Prop :=
  ∀ before value after, pre before → rawRun action context before = (.ok value, after) → post value after

theorem Triple.pure {context : CompileEnv × BlockEnv} {pre : BlockState → Prop} {post : α → BlockState → Prop}
    (value : α) (holds : ∀ state, pre state → post value state) :
    Triple context pre (pure value) post := by
  intro before result after ready ran
  cases ran
  exact holds before ready

theorem Triple.throw (context : CompileEnv × BlockEnv) (pre : BlockState → Prop) (post : α → BlockState → Prop)
    (error : CompileError) : Triple context pre (throw error : CompileM α) post := by
  intro before value after ready ran
  cases ran

theorem Triple.bind {context : CompileEnv × BlockEnv} {pre : BlockState → Prop}
    {middle : α → BlockState → Prop} {post : β → BlockState → Prop}
    {action : CompileM α} {next : α → CompileM β}
    (first : Triple context pre action middle) (later : ∀ value, Triple context (middle value) (next value) post) :
    Triple context pre (action >>= next) post := by
  intro before value after ready ran
  obtain ⟨first', between, ranFirst, ranNext⟩ := bind_ok ran
  exact later first' between value after (first before first' between ready ranFirst) ranNext

theorem Triple.consequence {context : CompileEnv × BlockEnv} {pre pre' : BlockState → Prop}
    {post post' : α → BlockState → Prop} {action : CompileM α}
    (holds : Triple context pre action post) (weaker : ∀ state, pre' state → pre state)
    (stronger : ∀ value state, post value state → post' value state) :
    Triple context pre' action post' := by
  intro before value after ready ran
  exact stronger value after (holds before value after (weaker before ready) ran)

theorem Triple.map {context : CompileEnv × BlockEnv} {pre : BlockState → Prop} {post : β → BlockState → Prop}
    {action : CompileM α} (f : α → β) (holds : Triple context pre action (fun value => post (f value))) :
    Triple context pre (f <$> action) post :=
  Triple.bind holds (fun value => Triple.pure (f value) (fun _ ready => ready))

theorem Triple.get (context : CompileEnv × BlockEnv) (pre : BlockState → Prop) :
    Triple context pre getBlockState (fun value state => value = state ∧ pre state) := by
  intro before value after ready ran
  cases ran
  exact ⟨rfl, ready⟩

theorem Triple.readBlock (context : CompileEnv × BlockEnv) (pre : BlockState → Prop) :
    Triple context pre getBlockEnv (fun value state => value = context.2 ∧ pre state) := by
  intro before value after ready ran
  cases ran
  exact ⟨rfl, ready⟩

theorem Triple.readCompile (context : CompileEnv × BlockEnv) (pre : BlockState → Prop) :
    Triple context pre getCompileEnv (fun value state => value = context.1 ∧ pre state) := by
  intro before value after ready ran
  cases ran
  exact ⟨rfl, ready⟩

theorem Triple.modify (context : CompileEnv × BlockEnv) (pre : BlockState → Prop)
    (update : BlockState → BlockState) :
    Triple context pre (modifyBlockState update) (fun _ state => ∃ before, pre before ∧ state = update before) := by
  intro before value after ready ran
  cases ran
  exact ⟨before, ready, rfl⟩

theorem Triple.modifyGet (context : CompileEnv × BlockEnv) (pre : BlockState → Prop)
    (update : BlockState → β × BlockState) :
    Triple context pre (modifyGetBlockState update)
      (fun value state => ∃ before, pre before ∧ (value, state) = update before) := by
  intro before value after ready ran
  cases ran
  exact ⟨before, ready, rfl⟩

theorem Triple.withBlockEnv {context : CompileEnv × BlockEnv} {pre : BlockState → Prop}
    {post : α → BlockState → Prop} {action : CompileM α} (update : BlockEnv → BlockEnv)
    (holds : Triple (context.1, update context.2) pre action post) :
    Triple context pre (withBlockEnv update action) post := by
  intro before value after ready ran
  rw [rawRun_withBlockEnv] at ran
  exact holds before value after ready ran

/-- A loop whose body keeps an invariant keeps it. -/
theorem Triple.forIn_list {context : CompileEnv × BlockEnv} (inv : β → BlockState → Prop)
    (items : List α) (initial : β) (body : α → β → CompileM (ForInStep β))
    (step : ∀ item acc, Triple context (inv acc) (body item acc) (fun result => inv result.value)) :
    Triple context (inv initial) (forIn items initial body) inv := by
  induction items generalizing initial with
  | nil => exact Triple.pure initial (fun _ ready => ready)
  | cons item rest ih =>
    rw [List.forIn_cons]
    refine Triple.bind (step item initial) (fun result => ?_)
    cases result with
    | done value => exact Triple.pure value (fun _ ready => ready)
    | yield value => exact ih value

theorem Triple.forIn_array {context : CompileEnv × BlockEnv} (inv : β → BlockState → Prop)
    (items : Array α) (initial : β) (body : α → β → CompileM (ForInStep β))
    (step : ∀ item acc, Triple context (inv acc) (body item acc) (fun result => inv result.value)) :
    Triple context (inv initial) (forIn items initial body) inv := by
  rw [← Array.forIn_toList]
  exact Triple.forIn_list inv items.toList initial body step

end Ix.CompileCert
