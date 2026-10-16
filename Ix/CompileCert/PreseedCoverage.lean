import Ix.CompileCert.PreseedState

/-! # The collector covers every universe of its roots

`Ix.CompileM.collectExprTablesStructural` walks a root expression in
preorder with a memo of visited keys (`Ix.Compile.ExactKey.PreseedKey`:
the exact expression and its complete parameter context, CQ2.8's C5) and
appends the positional universe of every level occurrence it reaches. A
successful collection of the roots contains the exact lowering
(`UniverseMeaning.lower`) of every level occurrence of every root under its
own parameter context (`roots_initial`), whatever the memo meets: a visited
key is a key whose subterm is already covered, except the pending ancestors
of the current node, which are larger (`PreseedKeys.CoveredBelow`).

CT-14's `PreseedKeys` and `PreseedUniverses` (the universe half of the
collector's coverage), ported over the merged universe meaning and the run
layer. -/

namespace Ix.CompileCert.PreseedKeys

open Ix.Compile.ExactKey
open Ix.CompileM

abbrev Seen := Std.HashMap PreseedKey Unit

theorem insert_other (seen : Seen) (stored queried : PreseedKey) (different : stored ≠ queried) :
    (seen.insert stored ()).contains queried = seen.contains queried := by
  rw [Std.HashMap.contains_insert]
  have miss : (stored == queried) = false := beq_eq_false_iff_ne.mpr different
  simp only [miss, Bool.false_or]

theorem insert_retains (seen : Seen) (stored queried : PreseedKey) (found : seen.contains queried = true) :
    (seen.insert stored ()).contains queried = true := by
  rw [Std.HashMap.contains_insert, found, Bool.or_true]

/-- The collector marks a parent before visiting its children. Restricting
coverage to smaller expressions permits these pending ancestors without
mistaking them for completed descendants. -/
def CoveredBelow (bound : Nat) (covered : PreseedKey → Prop) (seen : Seen) : Prop :=
  ∀ key, sizeOf key.expr < bound → seen.contains key = true → covered key

theorem CoveredBelow.empty (bound : Nat) (covered : PreseedKey → Prop) : CoveredBelow bound covered {} := by
  intro key _ found
  simp at found

theorem CoveredBelow.mono {bound : Nat} {first next : PreseedKey → Prop} {seen : Seen}
    (valid : CoveredBelow bound first seen) (growth : ∀ key, first key → next key) :
    CoveredBelow bound next seen :=
  fun key small found => growth key (valid key small found)

theorem CoveredBelow.restrict {before after : Nat} {covered : PreseedKey → Prop} {seen : Seen}
    (valid : CoveredBelow before covered seen) (bound : after ≤ before) : CoveredBelow after covered seen :=
  fun key small found => valid key (by omega) found

theorem CoveredBelow.insert {bound : Nat} {covered : PreseedKey → Prop} {seen : Seen}
    (valid : CoveredBelow bound covered seen) (key : PreseedKey)
    (ready : sizeOf key.expr < bound → covered key) : CoveredBelow bound covered (seen.insert key ()) := by
  intro query small found
  rw [Std.HashMap.contains_insert, Bool.or_eq_true] at found
  rcases found with same | prior
  · have same : key = query := eq_of_beq same
    subst query
    exact ready small
  · exact valid query small prior

theorem CoveredBelow.insert_above {bound : Nat} {covered : PreseedKey → Prop} {seen : Seen}
    (valid : CoveredBelow bound covered seen) (key : PreseedKey) (above : bound ≤ sizeOf key.expr) :
    CoveredBelow bound covered (seen.insert key ()) :=
  valid.insert key (fun small => by omega)

theorem CoveredBelow.lookup {covered : PreseedKey → Prop} {seen : Seen} (key : PreseedKey)
    (valid : CoveredBelow (sizeOf key.expr + 1) covered seen) (found : seen.contains key = true) :
    covered key :=
  valid key (by omega) found

theorem collect_hit (hint : Address) (mutualContext : Ix.MutCtx) (params : List Ix.Name) (source : Ix.Expr)
    (refs : Array Address) (univs : Array Ixon.Univ) (seen : Seen)
    (found : seen.contains ⟨source, params, hint⟩ = true) :
    collectExprTablesStructural hint mutualContext params source (refs, univs, seen) = pure (refs, univs, seen) := by
  rw [collectExprTablesStructural]
  simp only [found, ↓reduceIte]

/-- A root's collection runs the structural walk under the root's parameter
context, from a cleared universe memo. -/
theorem root_run (context : CompileEnv × BlockEnv) (before : BlockState) (source : Ix.Expr)
    (params : List Ix.Name) (initial : ExprTableCollection) :
    Ix.CompileCert.rawRun (withUnivCtx params (collectExprTables source (univParamsKey params) initial)) context before =
      Ix.CompileCert.rawRun (collectExprTablesStructural (univParamsKey params) context.2.mutCtx params source initial)
        (context.1, { context.2 with univCtx := params }) { before with univCache := {} } := rfl

end Ix.CompileCert.PreseedKeys

namespace Ix.CompileCert.PreseedUniverses

open Ix.CompileM Ix.CompileCert
open Ix.CompileCert.UniverseMeaning (UnivCacheExact lower)

/-- The universe memo stays exact on every run. -/
def CacheSafe (action : CompileM α) : Prop :=
  ∀ context before, UnivCacheExact before → UnivCacheExact (rawRun action context before).2

theorem CacheSafe.pure (value : α) : CacheSafe (pure value) := fun _ _ exactCache => exactCache

theorem CacheSafe.throw (error : CompileError) : CacheSafe (throw error : CompileM α) :=
  fun _ _ exactCache => exactCache

theorem CacheSafe.bind {action : CompileM α} {next : α → CompileM β}
    (first : CacheSafe action) (later : ∀ value, CacheSafe (next value)) : CacheSafe (action >>= next) := by
  intro context before exactCache
  have checked := first context before exactCache
  rw [rawRun_bind]
  cases ran : rawRun action context before with
  | mk outcome after =>
    rw [ran] at checked
    cases outcome with
    | error error => exact checked
    | ok value => exact later value context after checked

theorem CacheSafe.compileUniv (source : Ix.Level) : CacheSafe (Ix.CompileM.compileUniv source) :=
  fun context before exactCache => (UniverseMeaning.compileUniv_exact source context before exactCache).1

theorem CacheSafe.lookup (name : Ix.Name) : CacheSafe (lookupConstAddr name) := by
  intro context before exactCache
  rw [ExpressionState.lookupConstAddr_state]
  exact exactCache

theorem CacheSafe.blob (bytes : ByteArray) : CacheSafe (storeBlob bytes) := by
  intro context before exactCache
  have frame := (BlobWrites.storeBlob_preserves bytes context before).1
  have same := congrArg UnivCacheExact frame
  exact same.mpr exactCache

theorem CacheSafe.levels (levels : List Ix.Level) (initial : Array Ixon.Univ) :
    CacheSafe (collectExprTableUnivs levels initial) := by
  induction levels generalizing initial with
  | nil => exact CacheSafe.pure initial
  | cons level rest ih =>
    rw [collectExprTableUnivs]
    exact CacheSafe.bind (CacheSafe.compileUniv level) (fun value => ih (initial.push value))

theorem CacheSafe.structural (hint : Address) (mutualContext : MutCtx) (params : List Ix.Name)
    (source : Ix.Expr) (initial : ExprTableCollection) :
    CacheSafe (collectExprTablesStructural hint mutualContext params source initial) := by
  induction source generalizing initial
  all_goals try cases ‹Lean.Literal›
  all_goals
    rcases initial with ⟨refs, univs, seen⟩
    rw [collectExprTablesStructural]
    split
    · exact CacheSafe.pure _
    · with_reducible repeat' first
        | exact CacheSafe.pure _
        | exact CacheSafe.throw _
        | exact CacheSafe.compileUniv _
        | exact CacheSafe.lookup _
        | exact CacheSafe.blob _
        | exact CacheSafe.levels _ _
        | refine CacheSafe.bind ?_ (fun value => ?_)
        | dsimp only
        | split
        | apply_assumption

/-- The collected universes contain the exact lowering of `source`. -/
def Present (params : List Ix.Name) (univs : Array Ixon.Univ) (source : Ix.Level) : Prop :=
  ∃ value, lower params source = some value ∧ value ∈ univs

/-- Every level occurrence of an expression satisfies `P`. -/
def LevelsSatisfy (P : Ix.Level → Prop) : Ix.Expr → Prop
  | .bvar .. | .lit .. => True
  | .sort level _ => P level
  | .const _ levels _ => ∀ level ∈ levels, P level
  | .app fn arg _ => LevelsSatisfy P fn ∧ LevelsSatisfy P arg
  | .lam _ type body _ _ | .forallE _ type body _ _ => LevelsSatisfy P type ∧ LevelsSatisfy P body
  | .letE _ type value body _ _ => LevelsSatisfy P type ∧ LevelsSatisfy P value ∧ LevelsSatisfy P body
  | .proj _ _ value _ | .mdata _ value _ => LevelsSatisfy P value
  | .fvar .. | .mvar .. => False

theorem LevelsSatisfy.imp {P Q : Ix.Level → Prop} (weaker : ∀ level, P level → Q level) (source : Ix.Expr)
    (prior : LevelsSatisfy P source) : LevelsSatisfy Q source := by
  induction source with
  | bvar _ _ | lit _ _ => trivial
  | fvar _ _ | mvar _ _ => exact prior.elim
  | sort level _ => exact weaker level prior
  | const _ _ _ => exact fun level member => weaker level (prior level member)
  | app _ _ _ first second => exact ⟨first prior.1, second prior.2⟩
  | lam _ _ _ _ _ first second | forallE _ _ _ _ _ first second => exact ⟨first prior.1, second prior.2⟩
  | letE _ _ _ _ _ _ first second third => exact ⟨first prior.1, second prior.2.1, third prior.2.2⟩
  | proj _ _ _ _ child | mdata _ _ _ child => exact child prior

/-- Every level occurrence of an expression is present. -/
abbrev Covered (params : List Ix.Name) (univs : Array Ixon.Univ) : Ix.Expr → Prop :=
  LevelsSatisfy (Present params univs)

theorem Present.mono {params : List Ix.Name} {before after : Array Ixon.Univ} {source : Ix.Level}
    (prior : Present params before source) (growth : ∀ value ∈ before, value ∈ after) :
    Present params after source := by
  obtain ⟨value, lowered, member⟩ := prior
  exact ⟨value, lowered, growth value member⟩

theorem Present.value {params : List Ix.Name} {univs : Array Ixon.Univ} {source : Ix.Level}
    (present : Present params univs source) {value : Ixon.Univ} (lowered : lower params source = some value) :
    value ∈ univs := by
  obtain ⟨stored, exactValue, member⟩ := present
  have same := Option.some.inj (exactValue.symm.trans lowered)
  exact same ▸ member

theorem Covered.mono (params : List Ix.Name) (before after : Array Ixon.Univ)
    (growth : ∀ value ∈ before, value ∈ after) (source : Ix.Expr) (prior : Covered params before source) :
    Covered params after source :=
  LevelsSatisfy.imp (fun _ present => Present.mono present growth) source prior

theorem levels_correct (context : CompileEnv × BlockEnv) (levels : List Ix.Level)
    (before after : BlockState) (initial output : Array Ixon.Univ) (exactCache : UnivCacheExact before)
    (ran : rawRun (collectExprTableUnivs levels initial) context before = (.ok output, after)) :
    UnivCacheExact after ∧ (∀ value ∈ initial, value ∈ output) ∧
      ∀ level ∈ levels, Present context.2.univCtx output level := by
  induction levels generalizing before initial with
  | nil =>
    simp only [collectExprTableUnivs, rawRun_pure] at ran
    obtain ⟨result, rfl⟩ := Prod.mk.inj ran
    cases Except.ok.inj result
    exact ⟨exactCache, fun _ member => member, by simp⟩
  | cons level rest ih =>
    rw [collectExprTableUnivs] at ran
    obtain ⟨value, middle, firstRan, restRan⟩ := bind_ok ran
    have first := UniverseMeaning.compileUniv_exact level context before exactCache
    rw [firstRan] at first
    obtain ⟨finalCache, growth, covered⟩ := ih middle (initial.push value) first.1 restRan
    refine ⟨finalCache, fun value member => growth value (by simp [member]), ?_⟩
    intro query member
    rcases List.mem_cons.mp member with same | tail
    · subst query
      exact ⟨value, first.2 value rfl, growth value (by simp)⟩
    · exact covered query tail

/-- The visited keys a run added are covered. -/
def Added (before after : PreseedKeys.Seen) (univs : Array Ixon.Univ) : Prop :=
  ∀ key, after.contains key = true → before.contains key = true ∨ Covered key.params univs key.expr

theorem Added.refl (seen : PreseedKeys.Seen) (univs : Array Ixon.Univ) : Added seen seen univs :=
  fun _ found => Or.inl found

theorem Added.mono {before after : PreseedKeys.Seen} {first last : Array Ixon.Univ}
    (added : Added before after first) (growth : ∀ value ∈ first, value ∈ last) : Added before after last := by
  intro key found
  rcases added key found with prior | covered
  · exact Or.inl prior
  · exact Or.inr (Covered.mono key.params first last growth key.expr covered)

theorem Added.trans {before middle after : PreseedKeys.Seen} {first last : Array Ixon.Univ}
    (head : Added before middle first) (tail : Added middle after last)
    (growth : ∀ value ∈ first, value ∈ last) : Added before after last := by
  intro key found
  rcases tail key found with prior | covered
  · exact head.mono growth key prior
  · exact Or.inr covered

theorem Added.close_parent (key : Ix.Compile.ExactKey.PreseedKey)
    {before after : PreseedKeys.Seen} {univs : Array Ixon.Univ}
    (children : Added (before.insert key ()) after univs)
    (parent : Covered key.params univs key.expr) : Added before after univs := by
  intro query found
  rcases children query found with pending | covered
  · rw [Std.HashMap.contains_insert, Bool.or_eq_true] at pending
    rcases pending with same | old
    · have same : key = query := eq_of_beq same
      subst query
      exact Or.inr parent
    · exact Or.inl old
  · exact Or.inr covered

/-- Every visited key smaller than `source` is covered. -/
def Ready (source : Ix.Expr) (acc : ExprTableCollection) : Prop :=
  PreseedKeys.CoveredBelow (sizeOf source + 1) (fun key => Covered key.params acc.2.1 key.expr) acc.2.2

theorem Added.ready {before after : PreseedKeys.Seen} {first last : Array Ixon.Univ} (bound : Nat)
    (ready : PreseedKeys.CoveredBelow bound (fun key => Covered key.params first key.expr) before)
    (added : Added before after last) (growth : ∀ value ∈ first, value ∈ last) :
    PreseedKeys.CoveredBelow bound (fun key => Covered key.params last key.expr) after := by
  intro key small found
  rcases added key found with prior | covered
  · exact Covered.mono key.params first last growth key.expr (ready key small prior)
  · exact covered

structure Result (params : List Ix.Name) (source : Ix.Expr) (before after : ExprTableCollection) : Prop where
  grows : ∀ value ∈ before.2.1, value ∈ after.2.1
  covered : Covered params after.2.1 source
  added : Added before.2.2 after.2.2 after.2.1

theorem Result.cached (hint : Address) (params : List Ix.Name) (source : Ix.Expr) (acc : ExprTableCollection)
    (ready : Ready source acc) (hit : acc.2.2.contains ⟨source, params, hint⟩ = true) :
    Result params source acc acc :=
  ⟨fun _ member => member, PreseedKeys.CoveredBelow.lookup ⟨source, params, hint⟩ ready hit, Added.refl _ _⟩

theorem Result.insert (hint : Address) (params : List Ix.Name) (source : Ix.Expr) (before : ExprTableCollection)
    (refs : Array Address) (univs : Array Ixon.Univ)
    (growth : ∀ value ∈ before.2.1, value ∈ univs) (covered : Covered params univs source) :
    Result params source before (refs, univs, before.2.2.insert ⟨source, params, hint⟩ ()) :=
  ⟨growth, covered, Added.close_parent ⟨source, params, hint⟩ (Added.refl _ _) covered⟩

theorem prepare_child (hint : Address) (params : List Ix.Name) (parent child : Ix.Expr) (acc : ExprTableCollection)
    (ready : Ready parent acc) (smaller : sizeOf child < sizeOf parent) :
    Ready child (acc.1, acc.2.1, acc.2.2.insert ⟨parent, params, hint⟩ ()) := by
  have restricted := ready.restrict (after := sizeOf child + 1) (by omega)
  exact restricted.insert_above ⟨parent, params, hint⟩ (by dsimp only; omega)

theorem cached_run (context : CompileEnv × BlockEnv) (before after : BlockState)
    (hint : Address) (mutualContext : MutCtx) (params : List Ix.Name) (source : Ix.Expr)
    (initial output : ExprTableCollection) (ready : Ready source initial)
    (hit : initial.2.2.contains ⟨source, params, hint⟩ = true)
    (ran : rawRun (collectExprTablesStructural hint mutualContext params source initial) context before =
      (.ok output, after)) :
    Result params source initial output := by
  rcases initial with ⟨refs, univs, seen⟩
  rw [PreseedKeys.collect_hit hint mutualContext params source refs univs seen hit, rawRun_pure] at ran
  cases Except.ok.inj (congrArg Prod.fst ran)
  exact Result.cached hint params source _ ready hit

section Collection

variable (context : CompileEnv × BlockEnv) (hint : Address) (mutualContext : MutCtx) (params : List Ix.Name)
local notation "collector" => collectExprTablesStructural hint mutualContext params

def Correct (source : Ix.Expr) : Prop :=
  ∀ (before after : BlockState) (initial output : ExprTableCollection),
    UnivCacheExact before → Ready source initial →
    rawRun (collector source initial) context before = (.ok output, after) → Result params source initial output

theorem cache_after (source : Ix.Expr) (initial output : ExprTableCollection) (before after : BlockState)
    (exactCache : UnivCacheExact before)
    (ran : rawRun (collector source initial) context before = (.ok output, after)) :
    UnivCacheExact after := by
  have checked := CacheSafe.structural hint mutualContext params source initial context before exactCache
  rw [ran] at checked
  exact checked

theorem binary (parent first last : Ix.Expr)
    (firstCorrect : Correct context hint mutualContext params first)
    (lastCorrect : Correct context hint mutualContext params last)
    (firstSmall : sizeOf first < sizeOf parent) (lastSmall : sizeOf last < sizeOf parent)
    (assemble : ∀ univs, Covered params univs first → Covered params univs last → Covered params univs parent)
    (before after : BlockState) (initial output : ExprTableCollection)
    (exactCache : UnivCacheExact before) (ready : Ready parent initial)
    (ran : rawRun (do
      let middle ← collector first (initial.1, initial.2.1, initial.2.2.insert ⟨parent, params, hint⟩ ())
      collector last middle) context before = (.ok output, after)) : Result params parent initial output := by
  obtain ⟨middle, state, firstRan, lastRan⟩ := bind_ok ran
  have checkedFirst := firstCorrect before state _ middle exactCache
    (prepare_child hint params parent first initial ready firstSmall) firstRan
  have nextExact := cache_after context hint mutualContext params first _ middle before state exactCache firstRan
  have lastReady := checkedFirst.added.ready (sizeOf last + 1)
    (prepare_child hint params parent last initial ready lastSmall) checkedFirst.grows
  have checkedLast := lastCorrect state after middle output nextExact lastReady lastRan
  have parentCovered := assemble output.2.1
    (Covered.mono params middle.2.1 output.2.1 checkedLast.grows first checkedFirst.covered) checkedLast.covered
  exact ⟨fun value member => checkedLast.grows value (checkedFirst.grows value member), parentCovered,
    Added.close_parent ⟨parent, params, hint⟩ (checkedFirst.added.trans checkedLast.added checkedLast.grows)
      parentCovered⟩

theorem unary (parent child : Ix.Expr) (childCorrect : Correct context hint mutualContext params child)
    (smaller : sizeOf child < sizeOf parent) (before after : BlockState) (initial output : ExprTableCollection)
    (refs : Array Address) (univs : Array Ixon.Univ)
    (growth : ∀ value ∈ initial.2.1, value ∈ univs)
    (assemble : ∀ finalUnivs, (∀ value ∈ univs, value ∈ finalUnivs) →
      Covered params finalUnivs child → Covered params finalUnivs parent)
    (exactCache : UnivCacheExact before) (ready : Ready parent initial)
    (ran : rawRun (collector child (refs, univs, initial.2.2.insert ⟨parent, params, hint⟩ ())) context before =
      (.ok output, after)) :
    Result params parent initial output := by
  have childReady := (prepare_child hint params parent child initial ready smaller).mono
    (fun key covered => Covered.mono key.params initial.2.1 univs growth key.expr covered)
  have checked := childCorrect before after
    (refs, univs, initial.2.2.insert ⟨parent, params, hint⟩ ()) output exactCache childReady ran
  have parentCovered := assemble output.2.1 checked.grows checked.covered
  exact ⟨fun value member => checked.grows value (growth value member), parentCovered,
    Added.close_parent ⟨parent, params, hint⟩ checked.added parentCovered⟩

theorem ternary (parent first middle last : Ix.Expr)
    (firstCorrect : Correct context hint mutualContext params first)
    (middleCorrect : Correct context hint mutualContext params middle)
    (lastCorrect : Correct context hint mutualContext params last)
    (firstSmall : sizeOf first < sizeOf parent) (middleSmall : sizeOf middle < sizeOf parent)
    (lastSmall : sizeOf last < sizeOf parent)
    (assemble : ∀ univs, Covered params univs first → Covered params univs middle →
      Covered params univs last → Covered params univs parent)
    (before after : BlockState) (initial output : ExprTableCollection)
    (exactCache : UnivCacheExact before) (ready : Ready parent initial)
    (ran : rawRun (do
      let one ← collector first (initial.1, initial.2.1, initial.2.2.insert ⟨parent, params, hint⟩ ())
      let two ← collector middle one
      collector last two) context before = (.ok output, after)) : Result params parent initial output := by
  obtain ⟨one, stateOne, firstRan, tailRan⟩ := bind_ok ran
  obtain ⟨two, stateTwo, middleRan, lastRan⟩ := bind_ok tailRan
  have checkedFirst := firstCorrect before stateOne _ one exactCache
    (prepare_child hint params parent first initial ready firstSmall) firstRan
  have exactOne := cache_after context hint mutualContext params first _ one before stateOne exactCache firstRan
  have checkedMiddle := middleCorrect stateOne stateTwo one two exactOne
    (checkedFirst.added.ready (sizeOf middle + 1)
      (prepare_child hint params parent middle initial ready middleSmall) checkedFirst.grows) middleRan
  have exactTwo := cache_after context hint mutualContext params middle one two stateOne stateTwo exactOne middleRan
  have combined := checkedFirst.added.trans checkedMiddle.added checkedMiddle.grows
  have growth : ∀ value ∈ initial.2.1, value ∈ two.2.1 :=
    fun value member => checkedMiddle.grows value (checkedFirst.grows value member)
  have checkedLast := lastCorrect stateTwo after two output exactTwo
    (combined.ready (sizeOf last + 1) (prepare_child hint params parent last initial ready lastSmall) growth) lastRan
  have parentCovered := assemble output.2.1
    (Covered.mono params one.2.1 output.2.1
      (fun value member => checkedLast.grows value (checkedMiddle.grows value member)) first checkedFirst.covered)
    (Covered.mono params two.2.1 output.2.1 checkedLast.grows middle checkedMiddle.covered) checkedLast.covered
  exact ⟨fun value member => checkedLast.grows value (growth value member), parentCovered,
    Added.close_parent ⟨parent, params, hint⟩ (combined.trans checkedLast.added checkedLast.grows) parentCovered⟩

theorem Correct.of_miss (source : Ix.Expr)
    (check : ∀ (before after : BlockState) (initial output : ExprTableCollection),
      UnivCacheExact before → Ready source initial →
      ¬initial.2.2.contains ⟨source, params, hint⟩ = true →
      rawRun (collector source initial) context before = (.ok output, after) → Result params source initial output) :
    Correct context hint mutualContext params source := by
  intro before after initial output exactCache ready ran
  by_cases hit : initial.2.2.contains ⟨source, params, hint⟩ = true
  · exact cached_run context before after hint mutualContext params source initial output ready hit ran
  · exact check before after initial output exactCache ready hit ran

theorem collect_correct (aligned : context.2.univCtx = params) (source : Ix.Expr) :
    Correct context hint mutualContext params source := by
  induction source
  all_goals
    apply Correct.of_miss
    intro before after initial output exactCache ready missing ran
    rcases initial with ⟨refs, univs, seen⟩
    rw [collectExprTablesStructural] at ran
    simp only [missing, Bool.false_eq_true, ↓reduceIte] at ran
  case bvar index hash =>
    rw [rawRun_pure] at ran
    cases Except.ok.inj (congrArg Prod.fst ran)
    exact Result.insert hint params _ _ _ _ (fun _ member => member) True.intro
  case fvar name hash => cases ran
  case mvar name hash => cases ran
  case sort level hash =>
    obtain ⟨value, middle, compiled, returned⟩ := bind_ok ran
    rw [rawRun_pure] at returned
    cases Except.ok.inj (congrArg Prod.fst returned)
    apply Result.insert hint params _ _ _ _ (fun _ member => by simp [member])
    have lowered := UniverseMeaning.compileUniv_value level context before exactCache (congrArg Prod.fst compiled)
    rw [aligned] at lowered
    exact ⟨value, lowered, by simp⟩
  case const name levels hash =>
    obtain ⟨values, middle, levelsRan, tailRan⟩ := bind_ok ran
    have checked := levels_correct context levels.toList before middle univs values exactCache levelsRan
    have coverage : ∀ level ∈ levels, Present params values level := by
      intro level member
      simpa only [aligned] using checked.2.2 level (by simpa using member)
    by_cases external : (mutualContext.get? name).isNone = true
    · simp only [external, ↓reduceIte] at tailRan
      obtain ⟨address, named, _, returned⟩ := bind_ok tailRan
      rw [rawRun_pure] at returned
      cases Except.ok.inj (congrArg Prod.fst returned)
      exact Result.insert hint params _ _ _ _ checked.2.1 coverage
    · rw [ite_eq_right external, rawRun_pure] at tailRan
      cases Except.ok.inj (congrArg Prod.fst tailRan)
      exact Result.insert hint params _ _ _ _ checked.2.1 coverage
  case app first last hash firstIH lastIH =>
    exact binary context hint mutualContext params (.app first last hash) first last firstIH lastIH
      (by simp_wf; omega) (by simp_wf; omega) (fun _ a b => ⟨a, b⟩) before after _ output exactCache ready ran
  case lam name type body info hash typeIH bodyIH =>
    exact binary context hint mutualContext params (.lam name type body info hash) type body typeIH bodyIH
      (by simp_wf; omega) (by simp_wf; omega) (fun _ a b => ⟨a, b⟩) before after _ output exactCache ready ran
  case forallE name type body info hash typeIH bodyIH =>
    exact binary context hint mutualContext params (.forallE name type body info hash) type body typeIH bodyIH
      (by simp_wf; omega) (by simp_wf; omega) (fun _ a b => ⟨a, b⟩) before after _ output exactCache ready ran
  case letE name type value body nonDep hash typeIH valueIH bodyIH =>
    exact ternary context hint mutualContext params (.letE name type value body nonDep hash)
      type value body typeIH valueIH bodyIH (by simp_wf; omega) (by simp_wf; omega) (by simp_wf; omega)
      (fun _ a b c => ⟨a, b, c⟩) before after _ output exactCache ready ran
  case lit literal hash =>
    cases literal
    all_goals
      obtain ⟨address, middle, _, returned⟩ := bind_ok ran
      rw [rawRun_pure] at returned
      cases Except.ok.inj (congrArg Prod.fst returned)
      exact Result.insert hint params _ _ _ _ (fun _ member => member) True.intro
  case mdata metadata child hash childIH =>
    exact unary context hint mutualContext params (.mdata metadata child hash) child childIH
      (by simp_wf; omega) before after _ output refs univs (fun _ member => member)
      (fun _ _ covered => covered) exactCache ready ran
  case proj name index child hash childIH =>
    obtain ⟨address, middle, looked, childRan⟩ := bind_ok ran
    have same := ExpressionState.lookupConstAddr_state name context before
    rw [looked] at same
    dsimp only at same
    subst middle
    exact unary context hint mutualContext params (.proj name index child hash) child childIH
      (by simp_wf; omega) before after _ output (refs.push address) univs (fun _ member => member)
      (fun _ _ covered => covered) exactCache ready childRan

end Collection

def Complete (acc : ExprTableCollection) : Prop :=
  ∀ key, acc.2.2.contains key = true → Covered key.params acc.2.1 key.expr

theorem Complete.empty (refs : Array Address) (univs : Array Ixon.Univ) : Complete (refs, univs, {}) := by
  intro key found
  simp at found

theorem Complete.ready {acc : ExprTableCollection} (complete : Complete acc) (source : Ix.Expr) :
    Ready source acc :=
  fun key _ found => complete key found

theorem Complete.after {params : List Ix.Name} {source : Ix.Expr} {initial output : ExprTableCollection}
    (complete : Complete initial) (checked : Result params source initial output) : Complete output := by
  intro key found
  rcases checked.added key found with old | covered
  · exact Covered.mono key.params initial.2.1 output.2.1 checked.grows key.expr (complete key old)
  · exact covered

theorem root_correct (context : CompileEnv × BlockEnv) (before after : BlockState)
    (source : Ix.Expr) (params : List Ix.Name) (initial output : ExprTableCollection) (complete : Complete initial)
    (ran : rawRun (withUnivCtx params (collectExprTables source (univParamsKey params) initial)) context before =
      (.ok output, after)) :
    UnivCacheExact after ∧ Result params source initial output ∧ Complete output := by
  rw [PreseedKeys.root_run] at ran
  have initialExact := UniverseMeaning.univCacheExact_empty before
  have checked := collect_correct (context.1, { context.2 with univCtx := params }) (univParamsKey params)
    context.2.mutCtx params rfl source { before with univCache := {} } after initial output
    initialExact (complete.ready source) ran
  have finalExact := cache_after (context.1, { context.2 with univCtx := params }) (univParamsKey params)
    context.2.mutCtx params source initial output { before with univCache := {} } after initialExact ran
  exact ⟨finalExact, checked, complete.after checked⟩

theorem roots_correct (context : CompileEnv × BlockEnv) (roots : List (Ix.Expr × List Ix.Name))
    (before after : BlockState) (initial output : ExprTableCollection) (complete : Complete initial)
    (ran : rawRun (collectPreseedExprs roots initial) context before = (.ok output, after)) :
    (∀ value ∈ initial.2.1, value ∈ output.2.1) ∧
      (∀ root ∈ roots, Covered root.2 output.2.1 root.1) ∧ Complete output := by
  induction roots generalizing before initial with
  | nil =>
    simp only [collectPreseedExprs, rawRun_pure] at ran
    obtain ⟨result, _⟩ := Prod.mk.inj ran
    cases Except.ok.inj result
    exact ⟨fun _ member => member, by simp, complete⟩
  | cons root rest ih =>
    rcases root with ⟨source, params⟩
    rw [collectPreseedExprs] at ran
    obtain ⟨middle, state, rootRan, restRan⟩ := bind_ok ran
    obtain ⟨_, first, nextComplete⟩ := root_correct context before state source params initial middle complete rootRan
    obtain ⟨growth, tail, finalComplete⟩ := ih state middle nextComplete restRan
    refine ⟨fun value member => growth value (first.grows value member), ?_, finalComplete⟩
    intro root member
    rcases List.mem_cons.mp member with same | remaining
    · subst root
      exact Covered.mono params middle.2.1 output.2.1 growth source first.covered
    · exact tail root remaining

/-- **The collector covers every universe of its roots**: after a
successful collection, every level occurrence of every root has its exact
lowering, under the root's own parameter context, among the collected
universes. The root loop clears the universe memo on entry to each root, so
no memo premise is needed. -/
theorem roots_initial (context : CompileEnv × BlockEnv) (before after : BlockState)
    (roots : List (Ix.Expr × List Ix.Name)) (output : ExprTableCollection)
    (ran : rawRun (collectPreseedExprs roots (#[], #[], {})) context before = (.ok output, after)) :
    ∀ root ∈ roots, Covered root.2 output.2.1 root.1 :=
  (roots_correct context roots before after _ output (Complete.empty _ _) ran).2.1

end Ix.CompileCert.PreseedUniverses
