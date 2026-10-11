import Ix.CompileCert.Canon.QuerySelection
import Ix.CompileCert.Canon.AllocationHistory
import Ix.CompileCert.Canon.ExpansionScopeRun
import Ix.CompileCert.Canon.FreshFamilySeparation

/-!
Allocation cannot change the captured keep decision for an old query's
protected source references or already queued names. This is proved from
the actual class operation and its internally constructed history. The
protection thunk is the context's real thunk, with no substitute support set.

The source specialization derives the scope of every selected occurrence
and every alias attempted by its actual group. It then identifies complete
key conversions and complete registration states, including errors and
no-op insertions, across growth of the name table. Callback support is not
restricted. These are internal simulation facts, not new public premises.

This additive proof is uncompiled and unaudited. Initial raw-source paired
correspondence, paired class/constructor/queue transport, collapse,
representative independence and totality remain separate obligations.
-/

namespace Ix.CompileCert.Canon.QueryKeep

open Ix.Compile.Canon
open Ix (Name Expr)
open ExpansionHistory QuerySelection

private theorem register_typeNames (dedup : Dedup) (cls : Array Name) (original : Expr)
    (keyOf : Expr → Except String OccurrenceInput) (levels : Array Ix.Level)
    (specs : Array Expr) (aux : Name) (st : XSt) :
    (register dedup cls original keyOf levels specs aux st).typeNames = st.typeNames := by
  cases dedup with
  | compiler =>
    dsimp only [register]
    split <;> rfl
  | lean =>
    dsimp only [register]
    refine array_foldl_inv (fun q : XSt => q.typeNames = st.typeNames)
      _ ?_ _ _ rfl
    intro q alias retained
    repeat' (first | exact retained | split)

private theorem ctors_typeNames (cx : ExpansionCore.Ctx) (sourceName auxName : Name)
    (view : IndView) (externalParams : Nat) (levels : Array Ix.Level) (specs : Array Expr)
    (sourceNames : List Lean.Name) (st : XSt) :
    (ctors cx sourceName auxName view externalParams levels specs sourceNames st).1.typeNames =
      st.typeNames := by
  unfold ctors
  refine forIn_id_inv_array (fun q : XSt × Array XCtor => q.1.typeNames = st.typeNames)
    _ ?_ _ _ rfl
  intro sourceCtor current retained
  obtain ⟨cn,ct,nf⟩ := sourceCtor
  exact retained

/-- The real allocating class call inserts exactly its allocated auxiliary
in typeNames. All constructor and registration effects leave that table alone. -/
theorem event_typeNames {cx : ExpansionCore.Ctx} (event : Event cx) :
    event.after.typeNames = event.before.typeNames.insert event.name () := by
  have cache := sourceNames_eq cx event.before event.cache
  have yielded (value : XSt × Option Expr) :
      (pure (.yield value) : Id (ForInStep (XSt × Option Expr))).value = value := rfl
  unfold Event.after classStep
  rw [event.first]
  dsimp only
  rw [event.found]
  dsimp only
  simp only [cache]
  split <;> simp only [yielded, XSt.push, ctors_typeNames, register_typeNames] <;> rfl

/-- Structural freshness against the actual protection rules out precisely
the inserted key. No injectivity property of cached Name hashes is used. -/
theorem event_keeps_protected {cx : ExpansionCore.Ctx} (event : Event cx)
    (name : Name) (protectedName : keyName name ∈ cx.protect ()) :
    event.after.typeNames.contains name = event.before.typeNames.contains name := by
  have different : keyName event.name ≠ keyName name := by
    intro equal
    have impossible := event.sourceFree (keyName name) protectedName
    rw [equal, FreshFamilySeparation.prefix_refl] at impossible
    cases impossible
  rw [event_typeNames]
  simp only [NameTable.contains_insert, different, decide_false, Bool.false_or]

/-- Every actual history preserves old queued identities, irrespective of
callback answers, constructor naming, key errors or payload rewrites. -/
theorem history_contains_mono {cx : ExpansionCore.Ctx} {before after : XSt}
    {events : List (Event cx)} (history : History cx before events after)
    (name : Name) (queued : before.typeNames.contains name = true) :
    after.typeNames.contains name = true := by
  revert queued
  induction history with
  | refl => exact id
  | keyError => exact id
  | ctorType => exact id
  | allocation event =>
    intro queued
    rw [event_typeNames]
    exact NameTable.contains_insert_mono event.before.typeNames event.name name () queued
  | trans first second ihFirst ihSecond => exact fun queued => ihSecond (ihFirst queued)

/-- Protected source spellings retain both presence and absence, rather than
only the weaker monotonicity of a set. This is the allocator-to-key bridge. -/
theorem history_keeps_protected {cx : ExpansionCore.Ctx} {before after : XSt}
    {events : List (Event cx)} (history : History cx before events after)
    (name : Name) (protectedName : keyName name ∈ cx.protect ()) :
    after.typeNames.contains name = before.typeNames.contains name := by
  induction history with
  | refl => rfl
  | keyError => rfl
  | ctorType => rfl
  | allocation event => exact event_keeps_protected event name protectedName
  | trans first second ihFirst ihSecond => exact ihSecond.trans ihFirst

/-- Reference scope at a captured query. The left disjunct uses the exact
fixed context protection; the right uses the actual pre-state table. -/
def CapturedKnown (cx : ExpansionCore.Ctx) (before : XSt) (name : Name) : Prop :=
  keyName name ∈ cx.protect () ∨ before.typeNames.contains name = true

theorem history_keeps_known {cx : ExpansionCore.Ctx} {before after : XSt}
    {events : List (Event cx)} (history : History cx before events after)
    (name : Name) (known : CapturedKnown cx before name) :
    after.typeNames.contains name = before.typeNames.contains name := by
  rcases known with protectedName | queued
  · exact history_keeps_protected history name protectedName
  · exact (history_contains_mono history name queued).trans queued.symm

/-- Key equality depends only on actual constant/projection references.
All other inputs and the exact returned errors are retained. -/
theorem addrKey_keep_eq (ctx : List Name) (addr : Name → Option Address)
    (left right : Name → Bool) (expression : Expr)
    (agree : ∀ name ∈ sourceExprRefs expression, left name = right name) :
    addrKey ctx addr left expression = addrKey ctx addr right expression := by
  revert agree
  induction expression with
  | const name levels hash =>
    intro agree
    have same := agree name (by simp only [sourceExprRefs, List.mem_singleton])
    simp only [addrKey, addrRef, same]
  | app fn arg hash ihFn ihArg =>
    intro agree
    have fnAgree := fun name member => agree name (List.mem_append.mpr (.inl member))
    have argAgree := fun name member => agree name (List.mem_append.mpr (.inr member))
    simp only [addrKey, ihFn fnAgree, ihArg argAgree]
  | lam name type body info hash ihType ihBody =>
    intro agree
    have typeAgree := fun name member => agree name (List.mem_append.mpr (.inl member))
    have bodyAgree := fun name member => agree name (List.mem_append.mpr (.inr member))
    simp only [addrKey, ihType typeAgree, ihBody bodyAgree]
  | forallE name type body info hash ihType ihBody =>
    intro agree
    have typeAgree := fun name member => agree name (List.mem_append.mpr (.inl member))
    have bodyAgree := fun name member => agree name (List.mem_append.mpr (.inr member))
    simp only [addrKey, ihType typeAgree, ihBody bodyAgree]
  | letE name type value body nonDep hash ihType ihValue ihBody =>
    intro agree
    have typeAgree := fun name member =>
      agree name (List.mem_append.mpr (.inl (List.mem_append.mpr (.inl member))))
    have valueAgree := fun name member =>
      agree name (List.mem_append.mpr (.inl (List.mem_append.mpr (.inr member))))
    have bodyAgree := fun name member => agree name (List.mem_append.mpr (.inr member))
    simp only [addrKey, ihType typeAgree, ihValue valueAgree, ihBody bodyAgree]
  | mdata data body hash ihBody => exact ihBody
  | proj name index body hash ihBody =>
    intro agree
    have same := agree name List.mem_cons_self
    have bodyAgree := fun name member => agree name (List.mem_cons_of_mem _ member)
    simp only [addrKey, addrRef, same, ihBody bodyAgree]
  | _ => intro _; rfl

/-- Exactly the captured key function in replaceIfNested/resume, for both
optional-address branches. This is a proof-side name, not runtime replacement. -/
def keyAt (cx : ExpansionCore.Ctx) (names : NameSet) (expression : Expr) :
    Except String OccurrenceInput :=
  match cx.keyAddr? with
  | none => .ok (sourceOccurrence expression)
  | some addr => addrOccurrence cx.levelParams addr names.contains expression

/-- Complete Except equality, including advisory bucket and exact error text.
No successful normalization or cache lookup is required. -/
theorem history_keyAt_eq {cx : ExpansionCore.Ctx} {before after : XSt}
    {events : List (Event cx)} (history : History cx before events after)
    (expression : Expr) (scope : RefScope (CapturedKnown cx before) expression) :
    keyAt cx after.typeNames expression = keyAt cx before.typeNames expression := by
  unfold keyAt
  cases cx.keyAddr? with
  | none => rfl
  | some addr =>
    unfold addrOccurrence
    rw [addrKey_keep_eq cx.levelParams addr after.typeNames.contains before.typeNames.contains
      expression (fun name member => history_keeps_known history name (scope name member))]

/-- The actual unrestricted query constructs its own history. Its input may
take any early return, key error, cache hit or allocating class continuation. -/
theorem replaceIfNested_keyAt_eq (cx : ExpansionCore.Ctx) (np : Nat) (owner : Name)
    (query : Expr) (depth : Nat) (before : XSt) (cache : CacheCorrect cx before)
    (expression : Expr) (scope : RefScope (CapturedKnown cx before) expression) :
    keyAt cx (ExpansionCore.replaceIfNested cx np owner query depth before).2.typeNames expression =
      keyAt cx before.typeNames expression := by
  obtain ⟨events,history⟩ := replaceIfNested_history cx np owner query depth before cache
  exact history_keyAt_eq history expression scope

/-- Existing actual-source reachability discharges protection membership;
generated queued names use the other disjunct. No new source restriction. -/
theorem runKnown_captured {cx : XCtx} {state : XSt} {name : Name}
    (known : RunKnown cx state name) :
    CapturedKnown (ExpansionCore.Ctx.ofSource cx) state name := by
  rcases known with source | queued
  · exact .inl (sourceContext_reachable_done cx.source cx.sourceMembers cx.groupOf.blocks source).1
  · exact .inr queued

/-- Source scope and its cache invariant are the ones established by the
real initializer/queue. This retains the full actual query result on all paths. -/
theorem source_replaceIfNested_keyAt_eq (cx : XCtx) (np : Nat) (owner : Name)
    (query : Expr) (depth : Nat) (before : XSt) (state : ExpansionScope cx before)
    (expression : Expr) (scope : RefScope (RunKnown cx before) expression) :
    keyAt (ExpansionCore.Ctx.ofSource cx)
        (replaceIfNested cx np owner query depth before).2.typeNames expression =
      keyAt (ExpansionCore.Ctx.ofSource cx) before.typeNames expression := by
  rw [CoreBridge.replaceIfNested_eq_core]
  exact replaceIfNested_keyAt_eq (ExpansionCore.Ctx.ofSource cx) np owner query depth before
    state.sourceCache expression (scope.mono (fun _ known => runKnown_captured known))

private theorem selectHead_some {ind? : Name → Option IndView} {names : NameSet}
    {head : Expr} {args : Array Expr} {depth : Nat} {request : Request}
    (selected : selectHead ind? names head args depth = some request) :
    ∃ hash, head = .const request.name request.levels hash ∧ request.args = args ∧
      names.contains request.name = false ∧ ind? request.name = some request.external := by
  cases head with
  | const name levels hash =>
    dsimp only [selectHead] at selected
    split at selected
    · cases selected
    · rename_i outside
      split at selected
      · cases selected
      · rename_i external found
        split at selected
        · cases selected
        · split at selected
          · cases selected
          · split at selected
            · cases selected
            · cases selected
              exact ⟨hash,rfl,rfl,Bool.eq_false_iff.mpr outside,found⟩
  | _ => cases selected

/-- Every actual selected source request and every attempted group alias is
reached. The lowered specs retain the current source-or-queued reference scope. -/
theorem select_source_scope (cx : XCtx) (before : XSt) (query : Expr) (depth : Nat)
    (lookup : cx.ind? = IndView.ofConst? cx.source.get?)
    (scope : RefScope (RunKnown cx before) query) {request : Request}
    (selected : select cx.ind? before.typeNames query depth = some request) :
    RunReach cx request.name ∧
      (∀ expression ∈ request.specs depth, RefScope (RunKnown cx before) expression) ∧
      ∀ cls ∈ cx.groupOf request.external, ∀ alias ∈ cls, RunReach cx alias := by
  obtain ⟨hash,head,args,outside,found⟩ := selectHead_some selected
  have reached := scope.externalQuery head outside
  refine ⟨reached,?_,?_⟩
  · have arguments : ∀ expression ∈ request.args, RefScope (RunKnown cx before) expression := by
      rw [args]
      exact scope.getAppFnArgs.2
    intro expression member
    obtain ⟨original,inExtract,rfl⟩ := Array.mem_map.mp member
    obtain ⟨index,bound,rfl⟩ := Array.mem_extract_iff_getElem.mp inExtract
    exact (arguments _ (Array.getElem_mem _)).lowerLoose depth 0
  · intro cls member alias included
    apply reached.groupMember (groups := cx.groupOf) _ member included
    simpa only [lookup] using found

/-- The complete actual occurrence and every alias key keep their captured
meaning after the actual query. No terminal-history alignment, successful
normalization, representative lookup or alias agreement is assumed. -/
theorem source_selected_keys (cx : XCtx) (np : Nat) (owner : Name)
    (query : Expr) (depth : Nat) (before : XSt) (state : ExpansionScope cx before)
    (lookup : cx.ind? = IndView.ofConst? cx.source.get?)
    (scope : RefScope (RunKnown cx before) query) {request : Request}
    (selected : select cx.ind? before.typeNames query depth = some request) :
    let core := ExpansionCore.Ctx.ofSource cx
    let after := (replaceIfNested cx np owner query depth before).2
    keyAt core after.typeNames (request.occurrence depth) =
      keyAt core before.typeNames (request.occurrence depth) ∧
      ∀ cls ∈ cx.groupOf request.external, ∀ alias ∈ cls,
        keyAt core after.typeNames (mkAppN (Expr.mkConst alias request.levels) (request.specs depth)) =
          keyAt core before.typeNames (mkAppN (Expr.mkConst alias request.levels) (request.specs depth)) := by
  dsimp only
  obtain ⟨head,specs,aliases⟩ := select_source_scope cx before query depth lookup scope selected
  have occurrenceScope (name : Name) (reached : RunReach cx name) :
      RefScope (RunKnown cx before)
        (mkAppN (Expr.mkConst name request.levels) (request.specs depth)) := by
    apply RefScope.mkAppN _ specs
    intro ref member
    have same : ref = name := by simpa only [refs_mkConst, List.mem_singleton] using member
    subst ref
    exact .inl reached
  constructor
  · exact source_replaceIfNested_keyAt_eq cx np owner query depth before state _
      (occurrenceScope request.name head)
  · intro cls member alias included
    exact source_replaceIfNested_keyAt_eq cx np owner query depth before state _
      (occurrenceScope alias (aliases cls member alias included))

private theorem foldl_congr_mem {α β : Type} (xs : List α) (left right : β → α → β)
    (agree : ∀ x ∈ xs, ∀ state, left state x = right state x) (state : β) :
    xs.foldl left state = xs.foldl right state := by
  revert state agree
  induction xs with
  | nil => intro _ _; rfl
  | cons head tail ih =>
    intro agree state
    simp only [List.foldl_cons]
    rw [agree head List.mem_cons_self state]
    exact ih (fun x member => agree x (List.mem_cons_of_mem _ member)) _

/-- Complete ordered registration equality, including the first error latch
and contains guards. Only the keys for actually attempted aliases are used. -/
theorem register_keyAt_eq (dedup : Dedup) (cls : Array Name) (original : Expr)
    (leftKey rightKey : Expr → Except String OccurrenceInput)
    (levels : Array Ix.Level) (specs : Array Expr) (aux : Name) (state : XSt)
    (agree : ∀ alias ∈ cls,
      leftKey (mkAppN (Expr.mkConst alias levels) specs) =
        rightKey (mkAppN (Expr.mkConst alias levels) specs)) :
    register dedup cls original leftKey levels specs aux state =
      register dedup cls original rightKey levels specs aux state := by
  cases dedup with
  | compiler => rfl
  | lean =>
    simp only [register, ← Array.foldl_toList]
    apply foldl_congr_mem
    intro alias member current
    rw [agree alias (by simpa only [Array.mem_toList_iff] using member)]

/-- The actual selected source query supplies every registration equality.
The registration state is arbitrary: every field is retained, and neither
failed conversion nor a no-op insertion is dropped from the alias fold. -/
theorem source_selected_registration (cx : XCtx) (np : Nat) (owner : Name)
    (query : Expr) (depth : Nat) (before : XSt) (state : ExpansionScope cx before)
    (lookup : cx.ind? = IndView.ofConst? cx.source.get?)
    (scope : RefScope (RunKnown cx before) query) {request : Request}
    (selected : select cx.ind? before.typeNames query depth = some request)
    (cls : Array Name) (member : cls ∈ cx.groupOf request.external)
    (aux : Name) (registrationState : XSt) :
    let core := ExpansionCore.Ctx.ofSource cx
    let after := (replaceIfNested cx np owner query depth before).2
    register cx.dedup cls (request.occurrence depth)
        (keyAt core after.typeNames) request.levels (request.specs depth) aux registrationState =
      register cx.dedup cls (request.occurrence depth)
        (keyAt core before.typeNames) request.levels (request.specs depth) aux registrationState := by
  dsimp only
  apply register_keyAt_eq
  exact (source_selected_keys cx np owner query depth before state lookup scope selected).2 cls member

/-- All actual eligibility outcomes, without a selected-success premise.
Rejected queries return the complete original state. A selected query has
its occurrence key and every full alias-registration call identified across
the actual allocation growth, whether those conversions succeed or fail.
The source/cache scope is internal data of the existing queue invariant. -/
theorem source_query_registration (cx : XCtx) (np : Nat) (owner : Name)
    (query : Expr) (depth : Nat) (before : XSt) (state : ExpansionScope cx before)
    (lookup : cx.ind? = IndView.ofConst? cx.source.get?)
    (scope : RefScope (RunKnown cx before) query) :
    let core := ExpansionCore.Ctx.ofSource cx
    let after := (replaceIfNested cx np owner query depth before).2
    match select cx.ind? before.typeNames query depth with
    | none => replaceIfNested cx np owner query depth before = (none,before)
    | some request =>
      keyAt core after.typeNames (request.occurrence depth) =
          keyAt core before.typeNames (request.occurrence depth) ∧
        ∀ cls ∈ cx.groupOf request.external, ∀ aux registrationState,
          register cx.dedup cls (request.occurrence depth)
              (keyAt core after.typeNames) request.levels (request.specs depth) aux registrationState =
            register cx.dedup cls (request.occurrence depth)
              (keyAt core before.typeNames) request.levels (request.specs depth) aux registrationState := by
  dsimp only
  cases selected : select cx.ind? before.typeNames query depth with
  | none => rw [source_replaceIfNested_eq_select, selected]
  | some request =>
    refine ⟨(source_selected_keys cx np owner query depth before state lookup scope selected).1,?_⟩
    intro cls member aux registrationState
    exact source_selected_registration cx np owner query depth before state lookup scope selected
      cls member aux registrationState

end Ix.CompileCert.Canon.QueryKeep
