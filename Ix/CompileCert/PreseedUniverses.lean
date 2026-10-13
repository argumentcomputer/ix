import Ix.CompileCert.UniverseExact
import Ix.CompileCert.PreseedReferences

/-! Successful production collection contains the exact positional universes
needed by every expression and root. Visited coverage uses each retained
key's full parameter context. The root loop's cache reset discharges the
initial raw-cache premise. Canonicalization, wire bounds and table insertion
remain separate stages. -/

namespace Ix.CompileCert.PreseedUniverses

open Ix Ix.CompileM Ix.CompileCert.HeadWriterFrame
open UniverseExact (CacheExact lower)

def CacheSafe (action : CompileM α) : Prop :=
  ∀ context before, CacheExact before → CacheExact (rawRun action context before).2

theorem CacheSafe.pure (value : α) : CacheSafe (pure value) := fun _ _ exactCache => exactCache
theorem CacheSafe.throw (error : CompileError) : CacheSafe (throw error : CompileM α) := fun _ _ exactCache => exactCache

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

theorem CacheSafe.compileUniv (source : Level) : CacheSafe (compileUniv source) :=
  fun context before exactCache => (UniverseExact.compileUniv_exact source context before exactCache).1

theorem CacheSafe.lookup (name : Name) : CacheSafe (lookupConstAddr name) := by
  intro context before exactCache
  rw [ExpressionState.lookupConstAddr_state]
  exact exactCache

theorem CacheSafe.blob (bytes : ByteArray) : CacheSafe (storeBlob bytes) := by
  intro context before exactCache
  have frame := (BlobWrites.storeBlob_preserves bytes context before).1
  have same := congrArg CacheExact frame
  exact same.mpr exactCache

theorem CacheSafe.levels (levels : List Level) (initial : Array Ixon.Univ) :
    CacheSafe (collectExprTableUnivs levels initial) := by
  induction levels generalizing initial with
  | nil => exact CacheSafe.pure initial
  | cons level rest ih =>
    rw [collectExprTableUnivs]
    exact CacheSafe.bind (CacheSafe.compileUniv level) (fun value => ih (initial.push value))

theorem CacheSafe.structural (hint : Address) (mutualContext : MutCtx) (params : List Name)
    (source : Expr) (initial : ExprTableCollection) :
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

def Present (params : List Name) (univs : Array Ixon.Univ) (source : Level) : Prop :=
  ∃ value, lower params source = some value ∧ value ∈ univs

def Covered (params : List Name) (univs : Array Ixon.Univ) : Expr → Prop
  | .bvar .. | .lit .. => True
  | .sort level _ => Present params univs level
  | .const _ levels _ => ∀ level ∈ levels, Present params univs level
  | .app fn arg _ => Covered params univs fn ∧ Covered params univs arg
  | .lam _ type body _ _ | .forallE _ type body _ _ => Covered params univs type ∧ Covered params univs body
  | .letE _ type value body _ _ => Covered params univs type ∧ Covered params univs value ∧ Covered params univs body
  | .proj _ _ value _ | .mdata _ value _ => Covered params univs value
  | .fvar .. | .mvar .. => False

theorem Present.mono {params : List Name} {before after : Array Ixon.Univ} {source : Level}
    (prior : Present params before source) (growth : ∀ value ∈ before, value ∈ after) : Present params after source := by
  obtain ⟨value, lowered, member⟩ := prior
  exact ⟨value, lowered, growth value member⟩

theorem Present.value {params : List Name} {univs : Array Ixon.Univ} {source : Level}
    (present : Present params univs source) {value : Ixon.Univ} (lowered : lower params source = some value) : value ∈ univs := by
  obtain ⟨stored, exactValue, member⟩ := present
  have same := Option.some.inj (exactValue.symm.trans lowered)
  exact same ▸ member

/-- A later successful compilation from any exact cache uses the universe
already represented in the collected array, including repeated parameters. -/
theorem Present.compiled (context : CompileEnv × BlockEnv) (before : BlockState) (source : Level)
    (univs : Array Ixon.Univ) (present : Present context.2.univCtx univs source)
    (exactCache : CacheExact before) (value : Ixon.Univ)
    (ran : (rawRun (compileUniv source) context before).1 = .ok value) : value ∈ univs :=
  present.value (UniverseExact.compileUniv_value source context before exactCache value ran)

theorem Covered.mono (params : List Name) (before after : Array Ixon.Univ)
    (growth : ∀ value ∈ before, value ∈ after) (source : Expr) (prior : Covered params before source) :
    Covered params after source := by
  induction source with
  | bvar _ _ | lit _ _ => trivial
  | fvar _ _ | mvar _ _ => exact prior.elim
  | sort _ _ => exact Present.mono prior growth
  | const _ _ _ => exact fun level member => Present.mono (prior level member) growth
  | app _ _ _ first second => exact ⟨first prior.1, second prior.2⟩
  | lam _ _ _ _ _ first second | forallE _ _ _ _ _ first second => exact ⟨first prior.1, second prior.2⟩
  | letE _ _ _ _ _ _ first second third => exact ⟨first prior.1, second prior.2.1, third prior.2.2⟩
  | proj _ _ _ _ child | mdata _ _ _ child => exact child prior

theorem levels_correct (context : CompileEnv × BlockEnv) (levels : List Level)
    (before after : BlockState) (initial output : Array Ixon.Univ) (exactCache : CacheExact before)
    (ran : rawRun (collectExprTableUnivs levels initial) context before = (.ok output, after)) :
    CacheExact after ∧ (∀ value ∈ initial, value ∈ output) ∧ ∀ level ∈ levels, Present context.2.univCtx output level := by
  induction levels generalizing before initial with
  | nil =>
    simp only [collectExprTableUnivs, rawRun_pure] at ran
    obtain ⟨result, rfl⟩ := Prod.mk.inj ran
    cases Except.ok.inj result
    exact ⟨exactCache, fun _ member => member, by simp⟩
  | cons level rest ih =>
    rw [collectExprTableUnivs] at ran
    obtain ⟨value, middle, firstRan, restRan⟩ := PreseedReferences.bind_ok _ _ context before output after ran
    have first := UniverseExact.compileUniv_exact level context before exactCache
    rw [firstRan] at first
    obtain ⟨finalCache, growth, covered⟩ := ih middle (initial.push value) first.1 restRan
    refine ⟨finalCache, fun value member => growth value (by simp [member]), ?_⟩
    intro query member
    rcases List.mem_cons.mp member with same | tail
    · subst query
      exact ⟨value, first.2 value rfl, growth value (by simp)⟩
    · exact covered query tail

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

def Ready (source : Expr) (acc : ExprTableCollection) : Prop :=
  PreseedKeys.CoveredBelow (sizeOf source + 1) (fun key => Covered key.params acc.2.1 key.expr) acc.2.2

theorem Added.ready {before after : PreseedKeys.Seen} {first last : Array Ixon.Univ} (bound : Nat)
    (ready : PreseedKeys.CoveredBelow bound (fun key => Covered key.params first key.expr) before)
    (added : Added before after last) (growth : ∀ value ∈ first, value ∈ last) :
    PreseedKeys.CoveredBelow bound (fun key => Covered key.params last key.expr) after := by
  intro key small found
  rcases added key found with prior | covered
  · exact Covered.mono key.params first last growth key.expr (ready key small prior)
  · exact covered

structure Result (params : List Name) (source : Expr) (before after : ExprTableCollection) : Prop where
  grows : ∀ value ∈ before.2.1, value ∈ after.2.1
  covered : Covered params after.2.1 source
  added : Added before.2.2 after.2.2 after.2.1

theorem Result.cached (hint : Address) (params : List Name) (source : Expr) (acc : ExprTableCollection)
    (ready : Ready source acc) (hit : acc.2.2.contains ⟨source, params, hint⟩ = true) : Result params source acc acc := by
  exact ⟨fun _ member => member, PreseedKeys.CoveredBelow.lookup ⟨source, params, hint⟩ ready hit, Added.refl _ _⟩

theorem Result.insert (hint : Address) (params : List Name) (source : Expr) (before : ExprTableCollection)
    (refs : Array Address) (univs : Array Ixon.Univ)
    (growth : ∀ value ∈ before.2.1, value ∈ univs) (covered : Covered params univs source) :
    Result params source before (refs, univs, before.2.2.insert ⟨source, params, hint⟩ ()) :=
  ⟨growth, covered, Added.close_parent ⟨source, params, hint⟩ (Added.refl _ _) covered⟩

theorem prepare_child (hint : Address) (params : List Name) (parent child : Expr) (acc : ExprTableCollection)
    (ready : Ready parent acc) (smaller : sizeOf child < sizeOf parent) :
    Ready child (acc.1, acc.2.1, acc.2.2.insert ⟨parent, params, hint⟩ ()) := by
  have restricted := ready.restrict (after := sizeOf child + 1) (by omega)
  exact restricted.insert_above ⟨parent, params, hint⟩ (by dsimp only; omega)

theorem cached_run (context : CompileEnv × BlockEnv) (before after : BlockState)
    (hint : Address) (mutualContext : MutCtx) (params : List Name) (source : Expr)
    (initial output : ExprTableCollection) (ready : Ready source initial)
    (hit : initial.2.2.contains ⟨source, params, hint⟩ = true)
    (ran : rawRun (collectExprTablesStructural hint mutualContext params source initial) context before = (.ok output, after)) :
    Result params source initial output := by
  rcases initial with ⟨refs, univs, seen⟩
  rw [PreseedKeys.collect_hit hint mutualContext params source refs univs seen hit, rawRun_pure] at ran
  cases Except.ok.inj (congrArg Prod.fst ran)
  exact Result.cached hint params source _ ready hit

section Collection

variable (context : CompileEnv × BlockEnv) (hint : Address) (mutualContext : MutCtx) (params : List Name)
local notation "collector" => collectExprTablesStructural hint mutualContext params

def Correct (source : Expr) : Prop :=
  ∀ (before after : BlockState) (initial output : ExprTableCollection),
    CacheExact before → Ready source initial →
    rawRun (collector source initial) context before = (.ok output, after) → Result params source initial output

theorem cache_after (source : Expr) (initial output : ExprTableCollection) (before after : BlockState)
    (exactCache : CacheExact before) (ran : rawRun (collector source initial) context before = (.ok output, after)) :
    CacheExact after := by
  have checked := CacheSafe.structural hint mutualContext params source initial context before exactCache
  rw [ran] at checked
  exact checked

theorem binary (parent first last : Expr)
    (firstCorrect : Correct context hint mutualContext params first)
    (lastCorrect : Correct context hint mutualContext params last)
    (firstSmall : sizeOf first < sizeOf parent) (lastSmall : sizeOf last < sizeOf parent)
    (assemble : ∀ univs, Covered params univs first → Covered params univs last → Covered params univs parent)
    (before after : BlockState) (initial output : ExprTableCollection)
    (exactCache : CacheExact before) (ready : Ready parent initial)
    (ran : rawRun (do
      let middle ← collector first (initial.1, initial.2.1, initial.2.2.insert ⟨parent, params, hint⟩ ())
      collector last middle) context before = (.ok output, after)) : Result params parent initial output := by
  obtain ⟨middle, state, firstRan, lastRan⟩ := PreseedReferences.bind_ok _ _ context before output after ran
  have checkedFirst := firstCorrect before state _ middle exactCache
    (prepare_child hint params parent first initial ready firstSmall) firstRan
  have nextExact := cache_after context hint mutualContext params first _ middle before state exactCache firstRan
  have lastReady := checkedFirst.added.ready (sizeOf last + 1)
    (prepare_child hint params parent last initial ready lastSmall) checkedFirst.grows
  have checkedLast := lastCorrect state after middle output nextExact lastReady lastRan
  have parentCovered := assemble output.2.1
    (Covered.mono params middle.2.1 output.2.1 checkedLast.grows first checkedFirst.covered) checkedLast.covered
  exact ⟨fun value member => checkedLast.grows value (checkedFirst.grows value member), parentCovered,
    Added.close_parent ⟨parent, params, hint⟩ (checkedFirst.added.trans checkedLast.added checkedLast.grows) parentCovered⟩

theorem unary (parent child : Expr) (childCorrect : Correct context hint mutualContext params child)
    (smaller : sizeOf child < sizeOf parent) (before after : BlockState) (initial output : ExprTableCollection)
    (refs : Array Address) (univs : Array Ixon.Univ)
    (growth : ∀ value ∈ initial.2.1, value ∈ univs)
    (assemble : ∀ finalUnivs, (∀ value ∈ univs, value ∈ finalUnivs) →
      Covered params finalUnivs child → Covered params finalUnivs parent)
    (exactCache : CacheExact before) (ready : Ready parent initial)
    (ran : rawRun (collector child (refs, univs, initial.2.2.insert ⟨parent, params, hint⟩ ())) context before = (.ok output, after)) :
    Result params parent initial output := by
  have childReady := (prepare_child hint params parent child initial ready smaller).mono
    (fun key covered => Covered.mono key.params initial.2.1 univs growth key.expr covered)
  have checked := childCorrect before after
    (refs, univs, initial.2.2.insert ⟨parent, params, hint⟩ ()) output exactCache childReady ran
  have parentCovered := assemble output.2.1 checked.grows checked.covered
  exact ⟨fun value member => checked.grows value (growth value member), parentCovered,
    Added.close_parent ⟨parent, params, hint⟩ checked.added parentCovered⟩

theorem ternary (parent first middle last : Expr)
    (firstCorrect : Correct context hint mutualContext params first)
    (middleCorrect : Correct context hint mutualContext params middle)
    (lastCorrect : Correct context hint mutualContext params last)
    (firstSmall : sizeOf first < sizeOf parent) (middleSmall : sizeOf middle < sizeOf parent)
    (lastSmall : sizeOf last < sizeOf parent)
    (assemble : ∀ univs, Covered params univs first → Covered params univs middle →
      Covered params univs last → Covered params univs parent)
    (before after : BlockState) (initial output : ExprTableCollection)
    (exactCache : CacheExact before) (ready : Ready parent initial)
    (ran : rawRun (do
      let one ← collector first (initial.1, initial.2.1, initial.2.2.insert ⟨parent, params, hint⟩ ())
      let two ← collector middle one
      collector last two) context before = (.ok output, after)) : Result params parent initial output := by
  obtain ⟨one, stateOne, firstRan, tailRan⟩ := PreseedReferences.bind_ok _ _ context before output after ran
  obtain ⟨two, stateTwo, middleRan, lastRan⟩ := PreseedReferences.bind_ok _ _ context stateOne output after tailRan
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

theorem Correct.of_miss (source : Expr)
    (check : ∀ (before after : BlockState) (initial output : ExprTableCollection),
      CacheExact before → Ready source initial →
      ¬initial.2.2.contains ⟨source, params, hint⟩ = true →
      rawRun (collector source initial) context before = (.ok output, after) → Result params source initial output) :
    Correct context hint mutualContext params source := by
  intro before after initial output exactCache ready ran
  by_cases hit : initial.2.2.contains ⟨source, params, hint⟩ = true
  · exact cached_run context before after hint mutualContext params source initial output ready hit ran
  · exact check before after initial output exactCache ready hit ran

theorem collect_correct (aligned : context.2.univCtx = params) (source : Expr) :
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
    obtain ⟨value, middle, compiled, returned⟩ := PreseedReferences.bind_ok _ _ context before output after ran
    rw [rawRun_pure] at returned
    cases Except.ok.inj (congrArg Prod.fst returned)
    apply Result.insert hint params _ _ _ _ (fun _ member => by simp [member])
    have lowered := UniverseExact.compileUniv_value level context before exactCache value (congrArg Prod.fst compiled)
    rw [aligned] at lowered
    exact ⟨value, lowered, by simp⟩
  case const name levels hash =>
    obtain ⟨values, middle, levelsRan, tailRan⟩ := PreseedReferences.bind_ok _ _ context before output after ran
    have checked := levels_correct context levels.toList before middle univs values exactCache levelsRan
    have coverage : ∀ level ∈ levels, Present params values level := by
      intro level member
      simpa only [aligned] using checked.2.2 level (by simpa using member)
    by_cases external : (mutualContext.get? name).isNone = true
    · simp only [external, ↓reduceIte] at tailRan
      obtain ⟨address, named, _, returned⟩ := PreseedReferences.bind_ok _ _ context middle output after tailRan
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
      obtain ⟨address, middle, _, returned⟩ := PreseedReferences.bind_ok _ _ context before output after ran
      rw [rawRun_pure] at returned
      cases Except.ok.inj (congrArg Prod.fst returned)
      exact Result.insert hint params _ _ _ _ (fun _ member => member) True.intro
  case mdata metadata child hash childIH =>
    exact unary context hint mutualContext params (.mdata metadata child hash) child childIH
      (by simp_wf; omega) before after _ output refs univs (fun _ member => member)
      (fun _ _ covered => covered) exactCache ready ran
  case proj name index child hash childIH =>
    obtain ⟨address, middle, looked, childRan⟩ := PreseedReferences.bind_ok _ _ context before output after ran
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

theorem Complete.ready {acc : ExprTableCollection} (complete : Complete acc) (source : Expr) : Ready source acc :=
  fun key _ found => complete key found

theorem Complete.after {params : List Name} {source : Expr} {initial output : ExprTableCollection}
    (complete : Complete initial) (checked : Result params source initial output) : Complete output := by
  intro key found
  rcases checked.added key found with old | covered
  · exact Covered.mono key.params initial.2.1 output.2.1 checked.grows key.expr (complete key old)
  · exact covered

theorem public_correct (context : CompileEnv × BlockEnv) (before after : BlockState)
    (hint : Address) (source : Expr) (initial output : ExprTableCollection)
    (exactCache : CacheExact before) (complete : Complete initial)
    (ran : rawRun (collectExprTables source hint initial) context before = (.ok output, after)) :
    Result context.2.univCtx source initial output :=
  collect_correct context hint context.2.mutCtx context.2.univCtx rfl source before after initial output
    exactCache (complete.ready source) ran

theorem root_correct (context : CompileEnv × BlockEnv) (before after : BlockState)
    (source : Expr) (params : List Name) (initial output : ExprTableCollection) (complete : Complete initial)
    (ran : rawRun (withUnivCtx params (collectExprTables source (univParamsKey params) initial)) context before = (.ok output, after)) :
    CacheExact after ∧ Result params source initial output ∧ Complete output := by
  rw [PreseedReferences.root_run] at ran
  have initialExact := UniverseExact.cache_empty before
  have checked := collect_correct (context.1, { context.2 with univCtx := params }) (univParamsKey params)
    context.2.mutCtx params rfl source { before with univCache := {} } after initial output
    initialExact (complete.ready source) ran
  have finalExact := cache_after (context.1, { context.2 with univCtx := params }) (univParamsKey params)
    context.2.mutCtx params source initial output { before with univCache := {} } after initialExact ran
  exact ⟨finalExact, checked, complete.after checked⟩

theorem roots_correct (context : CompileEnv × BlockEnv) (roots : List (Expr × List Name))
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
    obtain ⟨middle, state, rootRan, restRan⟩ := PreseedReferences.bind_ok _ _ context before output after ran
    obtain ⟨_, first, nextComplete⟩ := root_correct context before state source params initial middle complete rootRan
    obtain ⟨growth, tail, finalComplete⟩ := ih state middle nextComplete restRan
    refine ⟨fun value member => growth value (first.grows value member), ?_, finalComplete⟩
    intro root member
    rcases List.mem_cons.mp member with same | remaining
    · subst root
      exact Covered.mono params middle.2.1 output.2.1 growth source first.covered
    · exact tail root remaining

theorem public_initial (context : CompileEnv × BlockEnv) (before after : BlockState)
    (hint : Address) (source : Expr) (output : ExprTableCollection) (exactCache : CacheExact before)
    (ran : rawRun (collectExprTables source hint (#[], #[], {})) context before = (.ok output, after)) :
    Covered context.2.univCtx output.2.1 source :=
  (public_correct context before after hint source _ output exactCache (Complete.empty _ _) ran).covered

theorem worklist_initial (context : CompileEnv × BlockEnv) (before after : BlockState)
    (hint : Address) (source : Expr) (output : ExprTableCollection) (exactCache : CacheExact before)
    (ran : rawRun (collectExprTablesWorklist source hint (#[], #[], {})) context before = (.ok output, after)) :
    Covered context.2.univCtx output.2.1 source := by
  rw [← collectExprTables_eq_worklist] at ran
  exact public_initial context before after hint source output exactCache ran

/-- The production root loop clears raw universe caches on entry to each
root, so this endpoint needs no assumption on the initial universe cache. -/
theorem roots_initial (context : CompileEnv × BlockEnv) (before after : BlockState)
    (roots : List (Expr × List Name)) (output : ExprTableCollection)
    (ran : rawRun (collectPreseedExprs roots (#[], #[], {})) context before = (.ok output, after)) :
    ∀ root ∈ roots, Covered root.2 output.2.1 root.1 :=
  (roots_correct context roots before after _ output (Complete.empty _ _) ran).2.1

end Ix.CompileCert.PreseedUniverses
