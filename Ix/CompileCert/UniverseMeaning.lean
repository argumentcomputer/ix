import Ix.CompileCert.ExpressionFrame
import Ix.CompileCert.Translate
import Std.Data.HashMap.Lemmas

/-! Semantic correctness and success of the actual source-level compiler.
Exact cache keys include the complete positional context. Well-scoped levels
compile under a wire-sized parameter telescope, and successful runs preserve
the existing source evaluator for every aligned valuation. This concerns raw
universe compilation; canonicalization and table reading are separate steps. -/

namespace Ix.CompileCert.UniverseMeaning

open Ix (Name Level)
open Ix.CompileM Ix.Compile.ExactKey Ix.CompileCert.HeadWriterFrame

theorem nameIndex_correct {name : Name} {params : List Name} {index : Nat}
    (found : nameIndex name params = some index) : params[index]? = some name := by
  obtain ⟨bound, same, _⟩ := List.findIdx?_eq_some_iff_getElem.mp found
  exact List.getElem?_eq_some_iff.mpr ⟨bound, (nameEq_iff _ _).mp same⟩

/-- Direct positional compilation of source levels. All stored digests are
ignored by the relation; parameter identity is exact and slots fit the wire. -/
inductive Represents (params : List Name) : Level → Ixon.Univ → Prop where
  | zero (hash : Address) : Represents params (.zero hash) .zero
  | succ {source value} (hash : Address) : Represents params source value →
      Represents params (.succ source hash) (.succ value)
  | max {left right first second} (hash : Address) :
      Represents params left first → Represents params right second →
      Represents params (.max left right hash) (.max first second)
  | imax {left right first second} (hash : Address) :
      Represents params left first → Represents params right second →
      Represents params (.imax left right hash) (.imax first second)
  | param (name : Name) (hash : Address) (index : Nat)
      (found : params[index]? = some name) (bound : index < UInt64.size) :
      Represents params (.param name hash) (.var index.toUInt64)

def CacheSound (state : BlockState) : Prop :=
  ∀ key value, state.univCache.get? key = some value → Represents key.params key.level value

theorem cache_empty (state : BlockState) :
    CacheSound { state with univCache := {} } := by
  intro level value found
  simp at found

theorem cache_lookup_insert (state : BlockState) (source query : UnivKey) (value : Ixon.Univ) :
    (state.cacheUniv source value).univCache.get? query =
      if source = query then some value else state.univCache.get? query := by
  change (state.univCache.insert source value)[query]? = _
  simp only [Std.HashMap.getElem?_insert, beq_iff_eq]
  rfl

theorem cache_insert {state : BlockState} (prior : CacheSound state)
    (key : UnivKey) (value : Ixon.Univ) (correct : Represents key.params key.level value) :
    CacheSound (state.cacheUniv key value) := by
  intro query result found
  rw [cache_lookup_insert] at found
  split at found
  · rename_i same
    subst query
    cases Option.some.inj found
    exact correct
  · exact prior query result found

/-- Actual execution preserves the cache invariant even on errors. -/
def Safe (action : CompileM α) (context : CompileEnv × BlockEnv) (post : α → Prop) : Prop :=
  ∀ before, CacheSound before →
    CacheSound (rawRun action context before).2 ∧
      ∀ value, (rawRun action context before).1 = .ok value → post value

theorem Safe.pure (context : CompileEnv × BlockEnv) {post : α → Prop} {value : α}
    (good : post value) : Safe (pure value) context post := by
  intro before sound
  exact ⟨sound, by intro result same; cases Except.ok.inj same; exact good⟩

theorem Safe.throw (context : CompileEnv × BlockEnv) (error : CompileError) (post : α → Prop) :
    Safe (throw error) context post := by
  intro before sound
  exact ⟨sound, by intro value impossible; cases impossible⟩

theorem Safe.bind {action : CompileM α} {next : α → CompileM β}
    {context : CompileEnv × BlockEnv} {post : α → Prop} {result : β → Prop}
    (first : Safe action context post)
    (later : ∀ value, post value → Safe (next value) context result) :
    Safe (action >>= next) context result := by
  intro before sound
  have checked := first before sound
  rw [rawRun_bind]
  cases ran : rawRun action context before with
  | mk outcome after =>
    rw [ran] at checked
    cases outcome with
    | error error => exact ⟨checked.1, by intro value impossible; cases impossible⟩
    | ok value => exact later value (checked.2 value rfl) after checked.1

theorem Safe.get (context : CompileEnv × BlockEnv) : Safe getBlockState context CacheSound := by
  intro before sound
  exact ⟨sound, by intro result same; cases Except.ok.inj same; exact sound⟩

theorem Safe.readBlock (context : CompileEnv × BlockEnv) :
    Safe getBlockEnv context (fun value => value = context.2) := by
  intro before sound
  exact ⟨sound, by intro result same; exact (Except.ok.inj same).symm⟩

theorem Safe.cache (context : CompileEnv × BlockEnv) (key : UnivKey) (value : Ixon.Univ)
    (good : Represents key.params key.level value) :
    Safe (modifyBlockState (fun state => state.cacheUniv key value)) context (fun _ => True) := by
  intro before sound
  exact ⟨cache_insert sound key value good, by intros; trivial⟩

theorem Safe.checkedIndex (context : CompileEnv × BlockEnv) (table : String) (index : Nat) :
    Safe (checkedTableIndex table index) context
      (fun value => index < UInt64.size ∧ value = index.toUInt64) := by
  unfold checkedTableIndex
  split
  · exact Safe.pure context ⟨by assumption, rfl⟩
  · exact Safe.throw context _ _

theorem Safe.finish (context : CompileEnv × BlockEnv) (key : UnivKey) (value : Ixon.Univ)
    (good : Represents key.params key.level value) :
    Safe (do
      let result ← Pure.pure value
      modifyBlockState (fun state => state.cacheUniv key result)
      Pure.pure result) context (Represents key.params key.level) := by
  exact Safe.bind (Safe.pure context good) (fun result correct =>
    Safe.bind (Safe.cache context key result correct) (fun _ _ => Safe.pure context correct))

theorem Safe.throwBind (context : CompileEnv × BlockEnv) (error : CompileError)
    (next : α → CompileM β) (post : β → Prop) :
    Safe ((MonadExceptOf.throw error) >>= next) context post :=
  Safe.bind (Safe.throw context error (fun _ => False)) (fun _ impossible => impossible.elim)

theorem compileUniv_correct (source : Level) (context : CompileEnv × BlockEnv) :
    Safe (compileUniv source) context (Represents context.2.univCtx source) := by
  induction source <;> rw [compileUniv]
  all_goals
    apply Safe.bind (Safe.get context)
    intro state valid
    apply Safe.bind (Safe.readBlock context)
    intro block same
    subst block
    dsimp only
    split
    · rename_i value found
      exact Safe.pure context (valid _ _ found)
  · exact Safe.finish context _ _ (.zero _)
  · apply Safe.bind (by assumption)
    intro value good
    exact Safe.finish context _ _ (.succ _ good)
  · apply Safe.bind (by assumption)
    intro first goodFirst
    apply Safe.bind (by assumption)
    intro second goodSecond
    exact Safe.finish context _ _ (.max _ goodFirst goodSecond)
  · apply Safe.bind (by assumption)
    intro first goodFirst
    apply Safe.bind (by assumption)
    intro second goodSecond
    exact Safe.finish context _ _ (.imax _ goodFirst goodSecond)
  · rename_i name hash _ _
    split
    · rename_i index found
      exact Safe.bind (Safe.checkedIndex context "universe parameter" index) (fun value good =>
        Safe.finish context _ _ (good.2 ▸ Represents.param name hash index (nameIndex_correct found) good.1))
    · exact Safe.bind (Safe.readBlock context) (fun _ _ => Safe.throwBind context _ _ _)
  · exact Safe.throwBind context _ _ _

theorem Represents.eval {params : List Name} {source : Level} {value : Ixon.Univ}
    (correct : Represents params source value) (φ : Lean.Name → Nat) (ρ : UInt64 → Nat)
    (aligned : ∀ i name, params[i]? = some name → i < UInt64.size →
      φ (ixName name) = ρ i.toUInt64) :
    ixLevelEval φ source = some (univEval ρ value) := by
  induction correct <;> simp_all [ixLevelEval, univEval]
  exact aligned _ _ (by assumption) (by assumption)

/-- The actual compiler, including warm cache hits, preserves the existing
source-level evaluator under an aligned positional valuation. -/
theorem compileUniv_eval (source : Level) (context : CompileEnv × BlockEnv)
    (before : BlockState) (sound : CacheSound before) {value : Ixon.Univ}
    (compiled : (rawRun (compileUniv source) context before).1 = .ok value)
    (φ : Lean.Name → Nat) (ρ : UInt64 → Nat)
    (aligned : ∀ i name, context.2.univCtx[i]? = some name → i < UInt64.size →
      φ (ixName name) = ρ i.toUInt64) :
    ixLevelEval φ source = some (univEval ρ value) :=
  ((compileUniv_correct source context before sound).2 value compiled).eval φ ρ aligned

theorem compileUniv_empty_eval (source : Level) (context : CompileEnv × BlockEnv)
    (before : BlockState) {value : Ixon.Univ}
    (compiled : (rawRun (compileUniv source) context { before with univCache := {} }).1 = .ok value)
    (φ : Lean.Name → Nat) (ρ : UInt64 → Nat)
    (aligned : ∀ i name, context.2.univCtx[i]? = some name → i < UInt64.size →
      φ (ixName name) = ρ i.toUInt64) :
    ixLevelEval φ source = some (univEval ρ value) :=
  compileUniv_eval source context _ (cache_empty before) compiled φ ρ aligned

theorem compileUniv_source_eval (source : Level) (context : CompileEnv × BlockEnv)
    (before : BlockState) (sound : CacheSound before) {view : Lean.Level}
    (translated : ixLevel source = .ok view) {value : Ixon.Univ}
    (compiled : (rawRun (compileUniv source) context before).1 = .ok value)
    (φ : Lean.Name → Nat) (ρ : UInt64 → Nat)
    (aligned : ∀ i name, context.2.univCtx[i]? = some name → i < UInt64.size →
      φ (ixName name) = ρ i.toUInt64) :
    sourceLevelEval φ view = some (univEval ρ value) := by
  rw [ixLevel_eval translated φ]
  exact compileUniv_eval source context before sound compiled φ ρ aligned

/-- A source condition independent of whether compilation succeeds. -/
def Scoped (params : List Name) : Level → Prop
  | .zero _ => True
  | .succ level _ => Scoped params level
  | .max left right _ | .imax left right _ => Scoped params left ∧ Scoped params right
  | .param name _ => name ∈ params
  | .mvar .. => False

def Returns (action : CompileM α) (context : CompileEnv × BlockEnv) : Prop :=
  ∀ state, ∃ value, (rawRun action context state).1 = .ok value

theorem Returns.pure (context : CompileEnv × BlockEnv) (value : α) :
    Returns (pure value) context := by intro state; exact ⟨value, rfl⟩

theorem Returns.bind {action : CompileM α} {next : α → CompileM β}
    {context : CompileEnv × BlockEnv} (first : Returns action context)
    (later : ∀ value, Returns (next value) context) : Returns (action >>= next) context := by
  intro state
  obtain ⟨value, ran⟩ := first state
  rw [rawRun_bind]
  cases result : rawRun action context state with
  | mk outcome after =>
    rw [result] at ran
    cases ran
    exact later value after

theorem Returns.get (context : CompileEnv × BlockEnv) : Returns getBlockState context := by
  intro state; exact ⟨state, rfl⟩

theorem Returns.readBlock (context : CompileEnv × BlockEnv) : Returns getBlockEnv context := by
  intro state; exact ⟨context.2, rfl⟩

theorem Returns.finish (context : CompileEnv × BlockEnv) (key : UnivKey) (value : Ixon.Univ) :
    Returns (do
      let result ← Pure.pure value
      modifyBlockState (fun state => state.cacheUniv key result)
      Pure.pure result) context := by
  intro state
  exact ⟨value, rfl⟩

theorem nameIndex_exists {params : List Name} {name : Name} (member : name ∈ params) :
    ∃ index, nameIndex name params = some index ∧ index < params.length := by
  cases found : nameIndex name params with
  | none =>
    have absent := List.findIdx?_eq_none_iff.mp found
    have := absent name member
    have yes := (nameEq_iff name name).mpr rfl
    rw [yes] at this
    contradiction
  | some index =>
    exact ⟨index, rfl, (List.findIdx?_eq_some_iff_getElem.mp found).choose⟩

theorem rawRun_readBlock (context : CompileEnv × BlockEnv) (state : BlockState) :
    rawRun getBlockEnv context state = (.ok context.2, state) := rfl

/-- Well-scoped source levels compile successfully from every cache state.
The separate soundness theorem rules out incorrect values from a bad cache. -/
theorem compileUniv_returns (source : Level) (context : CompileEnv × BlockEnv)
    (bounded : context.2.univCtx.length ≤ UInt64.size)
    (scope : Scoped context.2.univCtx source) : Returns (compileUniv source) context := by
  induction source <;> simp only [Scoped] at *
  all_goals try contradiction
  all_goals
    intro state
    rw [compileUniv]
    simp only [rawRun_bind, rawRun_get, rawRun_readBlock]
    split
    · exact ⟨_, rfl⟩
  · exact Returns.finish context _ _ state
  · rename_i level hash ih _ _
    exact Returns.bind (ih scope) (fun value => Returns.finish context _ (.succ value)) state
  · rename_i left right hash ihLeft ihRight _ _
    exact Returns.bind (ihLeft scope.1) (fun first =>
      Returns.bind (ihRight scope.2) (fun second => Returns.finish context _ (.max first second))) state
  · rename_i left right hash ihLeft ihRight _ _
    exact Returns.bind (ihLeft scope.1) (fun first =>
      Returns.bind (ihRight scope.2) (fun second => Returns.finish context _ (.imax first second))) state
  · obtain ⟨index, found, bound⟩ := nameIndex_exists scope
    rw [found]
    have fits := Nat.lt_of_lt_of_le bound bounded
    simp only [checkedTableIndex, fits]
    exact Returns.finish context _ _ state

theorem compileUniv_total_correct (source : Level) (context : CompileEnv × BlockEnv)
    (bounded : context.2.univCtx.length ≤ UInt64.size)
    (scope : Scoped context.2.univCtx source) (before : BlockState) (sound : CacheSound before) :
    ∃ value after, rawRun (compileUniv source) context before = (.ok value, after) ∧
      CacheSound after ∧ Represents context.2.univCtx source value := by
  obtain ⟨value, success⟩ := compileUniv_returns source context bounded scope before
  have correct := compileUniv_correct source context before sound
  exact ⟨value, _, Prod.ext success rfl, correct.1, correct.2 value success⟩

/-- No compiler-success premise: a well-scoped source compiles from an empty
universe cache and retains its meaning for every aligned valuation. -/
theorem compileUniv_total_eval (source : Level) (context : CompileEnv × BlockEnv)
    (bounded : context.2.univCtx.length ≤ UInt64.size)
    (scope : Scoped context.2.univCtx source) (before : BlockState) :
    ∃ value after,
      rawRun (compileUniv source) context { before with univCache := {} } = (.ok value, after) ∧
      CacheSound after ∧
      ∀ (φ : Lean.Name → Nat) (ρ : UInt64 → Nat),
        (∀ i name, context.2.univCtx[i]? = some name → i < UInt64.size →
          φ (ixName name) = ρ i.toUInt64) →
        ixLevelEval φ source = some (univEval ρ value) := by
  obtain ⟨value, after, ran, sound, represented⟩ :=
    compileUniv_total_correct source context bounded scope _ (cache_empty before)
  exact ⟨value, after, ran, sound, represented.eval⟩

end Ix.CompileCert.UniverseMeaning
