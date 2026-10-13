import Ix.CompileCert.UniverseMeaning

/-! Exact positional universe lowering for the production compiler. The
cache invariant is derived from initialization and retained on all outcomes.
It strengthens semantic cache soundness without restricting parameter lists
to distinct names or changing the existing compiler theorem domains. -/

namespace Ix.CompileCert.UniverseExact

open Ix (Name Level)
open Ix.CompileM Ix.Compile.ExactKey Ix.CompileCert.HeadWriterFrame

/-- Exact positional lowering, including first-occurrence parameter lookup
and the production wire-index bound. It is independent of compiler success. -/
def lower (params : List Name) : Level → Option Ixon.Univ
  | .zero _ => some .zero
  | .succ level _ => do return .succ (← lower params level)
  | .max left right _ => do return .max (← lower params left) (← lower params right)
  | .imax left right _ => do return .imax (← lower params left) (← lower params right)
  | .param name _ => do
    let index ← nameIndex name params
    if index < UInt64.size then some (.var index.toUInt64) else none
  | .mvar .. => none

def CacheExact (state : BlockState) : Prop :=
  ∀ key value, state.univCache.get? key = some value → lower key.params key.level = some value

theorem cache_empty (state : BlockState) : CacheExact { state with univCache := {} } := by
  intro key value found
  simp at found

theorem cache_insert {state : BlockState} (prior : CacheExact state)
    (key : UnivKey) (value : Ixon.Univ) (exactValue : lower key.params key.level = some value) :
    CacheExact (state.cacheUniv key value) := by
  intro query result found
  rw [UniverseMeaning.cache_lookup_insert] at found
  split at found
  · rename_i same
    subst query
    cases Option.some.inj found
    exact exactValue
  · exact prior query result found

def Safe (action : CompileM α) (context : CompileEnv × BlockEnv) (post : α → Prop) : Prop :=
  ∀ before, CacheExact before → CacheExact (rawRun action context before).2 ∧
    ∀ value, (rawRun action context before).1 = .ok value → post value

theorem Safe.pure (context : CompileEnv × BlockEnv) {post : α → Prop} {value : α}
    (good : post value) : Safe (pure value) context post := by
  intro before valid
  exact ⟨valid, by intro result same; cases Except.ok.inj same; exact good⟩

theorem Safe.throw (context : CompileEnv × BlockEnv) (error : CompileError) (post : α → Prop) :
    Safe (throw error) context post := by
  intro before valid
  exact ⟨valid, by intro value bad; cases bad⟩

theorem Safe.bind {action : CompileM α} {next : α → CompileM β}
    {context : CompileEnv × BlockEnv} {post : α → Prop} {result : β → Prop}
    (first : Safe action context post) (later : ∀ value, post value → Safe (next value) context result) :
    Safe (action >>= next) context result := by
  intro before valid
  have checked := first before valid
  rw [rawRun_bind]
  cases ran : rawRun action context before with
  | mk outcome after =>
    rw [ran] at checked
    cases outcome with
    | error error => exact ⟨checked.1, by intro value bad; cases bad⟩
    | ok value => exact later value (checked.2 value rfl) after checked.1

theorem Safe.get (context : CompileEnv × BlockEnv) : Safe getBlockState context CacheExact := by
  intro before valid
  exact ⟨valid, by intro result same; cases Except.ok.inj same; exact valid⟩

theorem Safe.readBlock (context : CompileEnv × BlockEnv) :
    Safe getBlockEnv context (fun value => value = context.2) := by
  intro before valid
  exact ⟨valid, by intro result same; exact (Except.ok.inj same).symm⟩

theorem Safe.cache (context : CompileEnv × BlockEnv) (key : UnivKey) (value : Ixon.Univ)
    (exactValue : lower key.params key.level = some value) :
    Safe (modifyBlockState (fun state => state.cacheUniv key value)) context (fun _ => True) := by
  intro before valid
  exact ⟨cache_insert valid key value exactValue, by intros; trivial⟩

theorem Safe.checkedIndex (context : CompileEnv × BlockEnv) (table : String) (index : Nat) :
    Safe (checkedTableIndex table index) context (fun value => index < UInt64.size ∧ value = index.toUInt64) := by
  unfold checkedTableIndex
  split
  · exact Safe.pure context ⟨by assumption, rfl⟩
  · exact Safe.throw context _ _

theorem Safe.finish (context : CompileEnv × BlockEnv) (key : UnivKey) (value : Ixon.Univ)
    (exactValue : lower key.params key.level = some value) :
    Safe (do
      let result ← Pure.pure value
      modifyBlockState (fun state => state.cacheUniv key result)
      Pure.pure result) context (fun result => lower key.params key.level = some result) :=
  Safe.bind (Safe.pure context exactValue) (fun result correct =>
    Safe.bind (Safe.cache context key result correct) (fun _ _ => Safe.pure context correct))

theorem Safe.throwBind (context : CompileEnv × BlockEnv) (error : CompileError)
    (next : α → CompileM β) (post : β → Prop) :
    Safe ((MonadExceptOf.throw error) >>= next) context post :=
  Safe.bind (Safe.throw context error (fun _ => False)) (fun _ bad => bad.elim)

/-- Every successful production run has the exact same positional lowering,
including duplicate source parameters; errors retain cache exactness. -/
theorem compileUniv_exact (source : Level) (context : CompileEnv × BlockEnv) :
    Safe (compileUniv source) context (fun value => lower context.2.univCtx source = some value) := by
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
  · exact Safe.finish context _ _ rfl
  · apply Safe.bind (by assumption)
    intro value good
    exact Safe.finish context _ _ (by simp only [lower, good, bind, Option.bind, pure])
  · apply Safe.bind (by assumption)
    intro first firstGood
    apply Safe.bind (by assumption)
    intro second secondGood
    exact Safe.finish context _ _ (by simp only [lower, firstGood, secondGood, bind, Option.bind, pure])
  · apply Safe.bind (by assumption)
    intro first firstGood
    apply Safe.bind (by assumption)
    intro second secondGood
    exact Safe.finish context _ _ (by simp only [lower, firstGood, secondGood, bind, Option.bind, pure])
  · rename_i name hash _ _
    split
    · rename_i index found
      exact Safe.bind (Safe.checkedIndex context "universe parameter" index) (fun value good =>
        Safe.finish context _ _ (by simp only [lower, found, bind, Option.bind, good.1, ↓reduceIte, good.2]))
    · exact Safe.bind (Safe.readBlock context) (fun _ _ => Safe.throwBind context _ _ _)
  · exact Safe.throwBind context _ _ _

theorem lower_represents (params : List Name) (source : Level) (value : Ixon.Univ)
    (lowered : lower params source = some value) : UniverseMeaning.Represents params source value := by
  induction source generalizing value with
  | zero hash => cases Option.some.inj lowered; exact .zero hash
  | succ child hash ih =>
    cases step : lower params child with
    | none => simp [lower, step] at lowered
    | some out =>
      simp only [lower, step, bind, Option.bind, pure] at lowered
      cases Option.some.inj lowered
      exact .succ hash (ih out step)
  | max left right hash leftIH rightIH | imax left right hash leftIH rightIH =>
    cases first : lower params left with
    | none => simp [lower, first] at lowered
    | some leftOut =>
      cases second : lower params right with
      | none => simp [lower, first, second] at lowered
      | some rightOut =>
        simp only [lower, first, second, bind, Option.bind, pure] at lowered
        cases Option.some.inj lowered
        first
          | exact .max hash (leftIH leftOut first) (rightIH rightOut second)
          | exact .imax hash (leftIH leftOut first) (rightIH rightOut second)
  | param name hash =>
    cases found : nameIndex name params with
    | none => simp [lower, found] at lowered
    | some index =>
      by_cases bounded : index < UInt64.size
      · simp only [lower, found, bind, Option.bind, bounded, ↓reduceIte] at lowered
        cases Option.some.inj lowered
        exact .param name hash index (UniverseMeaning.nameIndex_correct found) bounded
      · simp [lower, found, bounded] at lowered
  | mvar name hash => cases lowered

theorem CacheExact.sound {state : BlockState} (exactCache : CacheExact state) : UniverseMeaning.CacheSound state :=
  fun key value found => lower_represents key.params key.level value (exactCache key value found)

theorem compileUniv_value (source : Level) (context : CompileEnv × BlockEnv)
    (before : BlockState) (exactCache : CacheExact before) (value : Ixon.Univ)
    (ran : (rawRun (compileUniv source) context before).1 = .ok value) :
    lower context.2.univCtx source = some value :=
  (compileUniv_exact source context before exactCache).2 value ran

theorem compileUniv_same (source : Level) (context : CompileEnv × BlockEnv)
    (first second : BlockState) (firstExact : CacheExact first) (secondExact : CacheExact second)
    (left right : Ixon.Univ)
    (leftRan : (rawRun (compileUniv source) context first).1 = .ok left)
    (rightRan : (rawRun (compileUniv source) context second).1 = .ok right) : left = right :=
  Option.some.inj ((compileUniv_value source context first firstExact left leftRan).symm.trans
    (compileUniv_value source context second secondExact right rightRan))

theorem compileUniv_total (source : Level) (context : CompileEnv × BlockEnv)
    (bounded : context.2.univCtx.length ≤ UInt64.size)
    (scope : UniverseMeaning.Scoped context.2.univCtx source) (before : BlockState) (exactCache : CacheExact before) :
    ∃ value after, rawRun (compileUniv source) context before = (.ok value, after) ∧
      CacheExact after ∧ lower context.2.univCtx source = some value := by
  obtain ⟨value, success⟩ := UniverseMeaning.compileUniv_returns source context bounded scope before
  have checked := compileUniv_exact source context before exactCache
  exact ⟨value, _, Prod.ext success rfl, checked.1, checked.2 value success⟩

end Ix.CompileCert.UniverseExact
