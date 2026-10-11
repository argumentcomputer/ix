import Ix.CompileCert.Canon.ExpansionScopeRun
import Ix.CompileCert.Canon.AllocationForest

namespace Ix.CompileCert.Canon
open Ix.Compile.Canon
open Ix.Compile.Canon.FreshFamilySeparation
open Ix (Name Expr)

/-- Every reserved suffix family lies below its auxiliary root. -/
theorem auxSuffixFamilies_prefix {aux : Name} {suffix : Lean.Name}
    (member : suffix ∈ auxSuffixFamilies aux) :
    (keyName aux).isPrefixOf suffix = true := by
  unfold auxSuffixFamilies at member
  obtain ⟨label,_,rfl⟩ := List.mem_map.mp member
  simp [Lean.Name.isPrefixOf,prefix_refl]

/-- The actual allocation lists, with a proof-side list of allocated auxiliary
roots. The list is extended exactly when the runtime reserves an auxiliary;
it is not a premise on source declarations. -/
structure AllocationState (cx : XCtx) (roots : List Lean.Name) (st : XSt) : Prop where
  rootKeys : st.auxToNested.entries.map (fun entry => keyName entry.1) = roots
  ctorKeys : st.auxCtorMap.entries.map (fun entry => keyName entry.1) = st.allocatedCtorRoots
  forest : AllocationForest (keyName (Name.mkStr cx.all0 "_nested")) roots st.allocatedCtorRoots
  rootsCover : ∀ root ∈ roots, root ∈ st.allocatedNames
  ctorsCover : ∀ ctor ∈ st.allocatedCtorRoots, ctor ∈ st.allocatedNames
  allocatedOnly : ∀ name ∈ st.allocatedNames, name ∈ roots ∨ name ∈ st.allocatedCtorRoots
  sourceFree : ∀ name ∈ st.allocatedNames, ∀ original ∈
    (sourceContext cx.source cx.sourceMembers cx.groupOf.blocks).protectedNames,
      name.isPrefixOf original = false
  suffixFree : ∀ ctor ∈ st.allocatedCtorRoots, ∀ aux : Name, keyName aux ∈ roots →
    ∀ suffix ∈ auxSuffixFamilies aux, Apart ctor suffix

/-- Freshness against the actual stored structural keys implies an absent
lookup. Cached name digests have no part in this argument. -/
theorem nameTable_absent_of_familyFree {α : Type} (table : NameTable α)
    (fresh : Name) (forbidden : List Lean.Name)
    (covers : ∀ name value, (name,value) ∈ table.entries → keyName name ∈ forbidden)
    (free : ∀ original ∈ forbidden, (keyName fresh).isPrefixOf original = false) :
    table.get? fresh = none := by
  cases found : table.get? fresh with
  | none => rfl
  | some value =>
    obtain ⟨name,member,same⟩ := nameLookup_some_mem found
    have impossible := free (keyName name) (covers name value member)
    rw [same,prefix_refl] at impossible
    cases impossible

/-- An absent structural key is prepended without filtering old entries. -/
theorem nameTable_insert_entries {α : Type} (table : NameTable α)
    (name : Name) (value : α) (absent : table.get? name = none) :
    (table.insert name value).entries = (name,value) :: table.entries := by
  simp [NameTable.insert,absent]

theorem AllocationState.empty (cx : XCtx) : AllocationState cx [] {} := by
  constructor
  · rfl
  · rfl
  · exact AllocationForest.empty _
  all_goals simp

/-- Fields outside the allocation histories and origin tables preserve this invariant. -/
theorem AllocationState.fields {cx : XCtx} {roots : List Lean.Name} {st next : XSt}
    (state : AllocationState cx roots st)
    (names : next.allocatedNames = st.allocatedNames)
    (ctors : next.allocatedCtorRoots = st.allocatedCtorRoots)
    (nested : next.auxToNested.entries = st.auxToNested.entries)
    (origins : next.auxCtorMap.entries = st.auxCtorMap.entries) :
    AllocationState cx roots next := by
  constructor
  · simpa only [nested] using state.rootKeys
  · simpa only [origins,ctors] using state.ctorKeys
  · simpa only [ctors] using state.forest
  · simpa only [names] using state.rootsCover
  · simpa only [names,ctors] using state.ctorsCover
  · simpa only [names,ctors] using state.allocatedOnly
  · simpa only [names] using state.sourceFree
  · simpa only [ctors] using state.suffixFree

/-- Reserving the actual fresh family preserves its finite forest and source
separation; availability is proved from the actual lists, not assumed. -/
theorem AllocationState.reserve {cx : XCtx} {roots : List Lean.Name} {st : XSt}
    (state : AllocationState cx roots st) (label : String) (occurrence : Expr) :
    let sources := (sourceContext cx.source cx.sourceMembers cx.groupOf.blocks).protectedNames
    let aux := freshFamily (st.allocatedNames ++ sources) (Name.mkStr cx.all0 "_nested") label
    AllocationState cx (keyName aux :: roots)
      { st with
        allocatedNames := keyName aux :: st.allocatedNames,
        auxToNested := st.auxToNested.insert aux occurrence } := by
  dsimp only
  have absent : st.auxToNested.get?
      (freshFamily (st.allocatedNames ++
        (sourceContext cx.source cx.sourceMembers cx.groupOf.blocks).protectedNames)
        (Name.mkStr cx.all0 "_nested") label) = none := by
    apply nameTable_absent_of_familyFree st.auxToNested _ (st.allocatedNames ++
      (sourceContext cx.source cx.sourceMembers cx.groupOf.blocks).protectedNames)
    · intro name value member
      apply List.mem_append_left
      apply state.rootsCover
      rw [← state.rootKeys]
      exact List.mem_map.mpr ⟨(name,value),member,rfl⟩
    · exact freshFamily_free _ _ _
  constructor
  · rw [nameTable_insert_entries _ _ _ absent,List.map_cons,state.rootKeys]
  · exact state.ctorKeys
  · exact state.forest.reserve _ (fun root member =>
      List.mem_append_left _ (state.rootsCover root member)) label
  · intro root member
    rcases List.mem_cons.mp member with rfl | old
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (state.rootsCover root old)
  · intro ctor member
    exact List.mem_cons_of_mem _ (state.ctorsCover ctor member)
  · intro name member
    rcases List.mem_cons.mp member with rfl | old
    · exact Or.inl List.mem_cons_self
    · rcases state.allocatedOnly name old with root | ctor
      · exact Or.inl (List.mem_cons_of_mem _ root)
      · exact Or.inr ctor
  · intro name member original protectedName
    rcases List.mem_cons.mp member with rfl | old
    · exact freshFamily_free _ _ _ original (List.mem_append_right _ protectedName)
    · exact state.sourceFree name old original protectedName
  · intro ctor member aux owned suffix suffixMember
    rcases List.mem_cons.mp owned with same | old
    · obtain ⟨owner,ownerMember,child,_⟩ := state.forest.ctorOwner ctor member
      have separate := freshFamily_apart_old_aux
        (st.allocatedNames ++ (sourceContext cx.source cx.sourceMembers cx.groupOf.blocks).protectedNames)
        (Name.mkStr cx.all0 "_nested") label owner
        (List.mem_append_left _ (state.rootsCover owner ownerMember))
        (state.forest.rootShape owner ownerMember)
      apply separate.symm.descendants child
      rw [← same]
      exact auxSuffixFamilies_prefix suffixMember
    · exact state.suffixFree ctor member aux old suffix suffixMember

/-- The source constructor query comes from the checked reference-scope
bridge. No prefix condition on source constructor names is required. -/
theorem AllocationState.constructor {cx : XCtx} {roots : List Lean.Name} {st : XSt}
    (state : AllocationState cx roots st) (aux source old : Name) (index : Nat)
    (owned : keyName aux ∈ roots)
    (protectedName : keyName source ∈
      (sourceContext cx.source cx.sourceMembers cx.groupOf.blocks).protectedNames) :
    let sources := (sourceContext cx.source cx.sourceMembers cx.groupOf.blocks).protectedNames
    let generated := freshCtorFamily (st.allocatedNames ++ sources) aux
      (nameReplacePrefix source old aux) index st.allocatedCtorRoots
    AllocationState cx roots { st with
      allocatedNames := keyName generated :: st.allocatedNames,
      allocatedCtorRoots := keyName generated :: st.allocatedCtorRoots,
      auxCtorMap := st.auxCtorMap.insert generated (source,aux) } := by
  dsimp only
  have absent : st.auxCtorMap.get?
      (freshCtorFamily (st.allocatedNames ++
        (sourceContext cx.source cx.sourceMembers cx.groupOf.blocks).protectedNames)
        aux (nameReplacePrefix source old aux) index st.allocatedCtorRoots) = none := by
    apply nameTable_absent_of_familyFree st.auxCtorMap _ (st.allocatedNames ++
      (sourceContext cx.source cx.sourceMembers cx.groupOf.blocks).protectedNames)
    · intro name value member
      apply List.mem_append_left
      apply state.ctorsCover
      rw [← state.ctorKeys]
      exact List.mem_map.mpr ⟨(name,value),member,rfl⟩
    · exact freshCtorFamily_free _ _ _ _ _
  constructor
  · exact state.rootKeys
  · rw [nameTable_insert_entries _ _ _ absent,List.map_cons,state.ctorKeys]
  · exact state.forest.addCtor _ aux source old index owned (List.mem_append_right _ protectedName)
  · intro root member
    exact List.mem_cons_of_mem _ (state.rootsCover root member)
  · intro ctor member
    rcases List.mem_cons.mp member with rfl | old
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (state.ctorsCover ctor old)
  · intro name member
    rcases List.mem_cons.mp member with rfl | old
    · exact Or.inr List.mem_cons_self
    · rcases state.allocatedOnly name old with root | ctor
      · exact Or.inl root
      · exact Or.inr (List.mem_cons_of_mem _ ctor)
  · intro name member original originalProtected
    rcases List.mem_cons.mp member with rfl | old
    · exact freshCtorFamily_free _ _ _ _ _ original (List.mem_append_right _ originalProtected)
    · exact state.sourceFree name old original originalProtected
  · intro ctor member other ownedOther suffix suffixMember
    rcases List.mem_cons.mp member with rfl | oldCtor
    · by_cases same : keyName aux = keyName other
      · apply freshCtorFamily_apart_suffix
        simpa only [auxSuffixFamilies,same] using suffixMember
      · have separate := auxRoot_apart_of_ne (state.forest.rootShape _ owned)
          (state.forest.rootShape _ ownedOther) same
        apply separate.descendants
        · exact (freshCtorFamily_owner _ aux source old index st.allocatedCtorRoots
            (List.mem_append_right _ protectedName)).1
        · exact auxSuffixFamilies_prefix suffixMember
    · exact state.suffixFree ctor oldCtor other ownedOther suffix suffixMember

/-- The allocation histories and origin tables are untouched by every actual cache branch. -/
theorem nestedSeen_allocations (dedup : Dedup) (original : Expr)
    (keyOf : Name → Except String OccurrenceInput) (cls : Array Name)
    (aux : Name) (st : XSt) :
    let result := nestedSeen dedup original keyOf cls aux st
    result.allocatedNames = st.allocatedNames ∧
      result.allocatedCtorRoots = st.allocatedCtorRoots ∧
      result.auxToNested.entries = st.auxToNested.entries ∧
      result.auxCtorMap.entries = st.auxCtorMap.entries := by
  unfold nestedSeen
  split
  · split <;> exact ⟨rfl,rfl,rfl,rfl⟩
  · refine array_foldl_inv (fun q : XSt => q.allocatedNames = st.allocatedNames ∧
      q.allocatedCtorRoots = st.allocatedCtorRoots ∧
      q.auxToNested.entries = st.auxToNested.entries ∧
      q.auxCtorMap.entries = st.auxCtorMap.entries) _ ?_ _ _ ⟨rfl,rfl,rfl,rfl⟩

    intro q alias previous
    repeat' first | exact previous | split

/-- The exact constructor loop extends the real constructor-root history
inside the already reserved auxiliary family. Every source query is protected
by the actual source closure, without a source-prefix assumption. -/
theorem nestedCtors_allocation (cx : XCtx) (sourceName auxName : Name) (view : IndView)
    (externalParams : Nat) (levels : Array Ix.Level) (specs : Array Expr)
    (sourceNames : List Lean.Name) (st : XSt) (roots : List Lean.Name)
    (sameSources : sourceNames =
      (sourceContext cx.source cx.sourceMembers cx.groupOf.blocks).protectedNames)
    (state : AllocationState cx roots st) (owned : keyName auxName ∈ roots)
    (protectedCtors : ∀ ctor ∈ view.ctors, keyName ctor.1 ∈ sourceNames) :
    AllocationState cx roots
      (nestedCtors cx sourceName auxName view externalParams levels specs sourceNames st).1 := by
  subst sourceNames
  unfold nestedCtors
  refine forIn_id_inv_array_mem (fun q : XSt × Array XCtor => AllocationState cx roots q.1)
    _ _ _ state ?_
  intro sourceCtor sourceMember q previous
  obtain ⟨cn,ct,nf⟩ := sourceCtor
  have update := previous.constructor auxName cn sourceName q.2.size owned
    (protectedCtors (cn,ct,nf) sourceMember)
  exact update.fields rfl rfl rfl rfl

/-- A real class step either allocates nothing or reserves exactly the next
auxiliary family and its constructor families. Reachability and scope are
internal query invariants, supplied by the enclosing actual query theorem. -/
theorem nestedClassStep_allocation (cx : XCtx) (owner : Name) (externalParams : Nat)
    (levels : Array Ix.Level) (specs : Array Expr) (original : Expr)
    (keyOf : Expr → Except String OccurrenceInput) (head : Name)
    (repl : Name → Expr) (cls : Array Name) (state next : XSt × Option Expr)
    (lookup : cx.ind? = IndView.ofConst? cx.source.get?)
    (scope : ExpansionScope cx state.1) (roots : List Lean.Name)
    (allocation : AllocationState cx roots state.1)
    (reached : ∀ name ∈ cls, RunReach cx name)
    (run : nestedClassStep cx owner externalParams levels specs original keyOf head repl cls state =
      .yield next) : ∃ nextRoots, AllocationState cx nextRoots next.1 := by
  unfold nestedClassStep at run
  split at run
  · rename_i name chosen
    split at run
    · rename_i view found
      let sourceNames := state.1.sourceNames cx
      let auxName := freshFamily (state.1.allocatedNames ++ sourceNames) (Name.mkStr cx.all0 "_nested")
        s!"{(namePretty name).replace "." "_"}_{state.1.nextAuxIdx}"
      let prepared : XSt := { state.1 with
        nextAuxIdx := state.1.nextAuxIdx + 1, sourceNames? := some sourceNames,
        allocatedNames := keyName auxName :: state.1.allocatedNames,
        auxToNested := state.1.auxToNested.insert auxName (mkAppN (Expr.mkConst name levels) specs) }
      let registered := nestedSeen cx.dedup original
        (fun alias => keyOf (mkAppN (Expr.mkConst alias levels) specs)) cls auxName prepared
      let result := nestedCtors cx name auxName view externalParams levels specs sourceNames registered
      let member : XMember := {
        name := auxName, sourceOwner := owner,
        typ := mkForalls cx.paramBinders
          (instantiatePiParams (substLevels view.levelParams levels view.type) externalParams specs),
        ctors := result.2, nParams := cx.nParams, nIndices := view.numIndices }
      change (if cls.contains head then ForInStep.yield (result.1.push member,some (repl auxName))
        else ForInStep.yield (result.1.push member,state.2)) = .yield next at run
      have sameState : next.1 = result.1.push member := by
        split at run <;> cases run <;> rfl
      rw [sameState]
      refine ⟨keyName auxName :: roots,?_⟩
      have preparedState : AllocationState cx (keyName auxName :: roots) prepared := by
        have reserve := allocation.reserve s!"{(namePretty name).replace "." "_"}_{state.1.nextAuxIdx}"
          (mkAppN (Expr.mkConst name levels) specs)

        dsimp only at reserve
        rw [← scope.sourceNames] at reserve
        exact reserve.fields rfl rfl rfl rfl
      have cacheFields := nestedSeen_allocations cx.dedup original
        (fun alias => keyOf (mkAppN (Expr.mkConst alias levels) specs)) cls auxName prepared
      have registeredState : AllocationState cx (keyName auxName :: roots) registered :=
        preparedState.fields cacheFields.1 cacheFields.2.1 cacheFields.2.2.1 cacheFields.2.2.2
      have actual : IndView.ofConst? cx.source.get? name = some view := by simpa [lookup] using found
      have nameReached := reached name (Array.mem_of_getElem? chosen)
      have resultState : AllocationState cx (keyName auxName :: roots) result.1 := by
        apply nestedCtors_allocation cx name auxName view externalParams levels specs sourceNames
          registered (keyName auxName :: roots) scope.sourceNames registeredState List.mem_cons_self
        intro ctor member
        rw [show sourceNames =
          (sourceContext cx.source cx.sourceMembers cx.groupOf.blocks).protectedNames from scope.sourceNames]
        exact (nameReached.viewCtor actual member).2.2
      exact resultState.fields rfl rfl rfl rfl
    · cases run
      exact ⟨roots,allocation⟩
  · cases run
    exact ⟨roots,allocation⟩


/-- The auxiliary-root history is internal proof data, reconstructed from the
actual successful allocation transitions. -/
def AllocationInvariant (cx : XCtx) (st : XSt) : Prop :=
  ∃ roots, AllocationState cx roots st

/-- The real class loop preserves both the scoped query context and its
finite allocation forest. Class reachability is derived from the actual
registered group, and the auxiliary history is extended by the actual step. -/
theorem nestedClasses_allocation (cx : XCtx) (np : Nat) (owner : Name)
    (levels : Array Ix.Level) (specs : Array Expr) (original : Expr)
    (keyOf : Expr → Except String OccurrenceInput) (head : Name)
    (repl : Name → Expr) (view : IndView) (st : XSt)
    (lookup : cx.ind? = IndView.ofConst? cx.source.get?)
    (query : RunReach cx head) (found : cx.ind? head = some view)
    (scope : ExpansionScope cx st)
    (parameters : ∀ b ∈ cx.paramBinders, BinderScope (RunReach cx) b)
    (arguments : ∀ e ∈ specs, RefScope (RunKnown cx st) e)
    (allocation : AllocationInvariant cx st) :
    AllocationInvariant cx
      (forIn (m := Id) (cx.groupOf view) (st,none)
        (nestedClassStep cx owner np levels specs original keyOf head repl)).1 := by
  have all :
      let result := forIn (m := Id) (cx.groupOf view) (st,none)
        (nestedClassStep cx owner np levels specs original keyOf head repl)
      ExpansionScope cx result.1 ∧ ExpansionFrame cx st result.1 ∧
        AllocationInvariant cx result.1 := by
    dsimp only
    refine forIn_id_inv_array_mem (fun state : XSt × Option Expr =>
      ExpansionScope cx state.1 ∧ ExpansionFrame cx st state.1 ∧
        AllocationInvariant cx state.1)
      _ _ _ ⟨scope,ExpansionFrame.refl cx st,allocation⟩ ?_
    intro cls member state invariant
    obtain ⟨next,step⟩ := nestedClassStep_yield cx owner np levels specs original keyOf head repl cls state
    rw [step]
    have reached : ∀ name ∈ cls, RunReach cx name := by
      intro name inClass
      apply query.groupMember (groups := cx.groupOf) ?_ member inClass
      simpa [lookup] using found
    have stepFrame := nestedClassStep_frame cx owner np levels specs original keyOf head repl cls state next step
    obtain ⟨roots,allocated⟩ := invariant.2.2
    refine ⟨nestedClassStep_expansionScope cx owner np levels specs original keyOf head repl cls state next
      lookup invariant.1 parameters ?_ reached step,
      invariant.2.1.trans stepFrame,
      nestedClassStep_allocation cx owner np levels specs original keyOf head repl cls state next
        lookup invariant.1 roots allocated reached step⟩
    intro e inSpecs
    exact (arguments e inSpecs).mono (fun _ known => known.frame invariant.2.1)
  exact all.2.2

private theorem allocation_id_pure {α : Type} (value : α) : (pure value : Id α) = value := rfl

/-- The actual nested query preserves the finite allocation forest. Its
source and expression premises are internal reference invariants already
derived by the real initializer and preserved by the actual queue. -/
theorem replaceIfNested_allocation (cx : XCtx) (np : Nat) (owner : Name)
    (e : Expr) (depth : Nat) (st : XSt)
    (lookup : cx.ind? = IndView.ofConst? cx.source.get?)
    (scope : ExpansionScope cx st)
    (parameters : ∀ b ∈ cx.paramBinders, BinderScope (RunReach cx) b)
    (expression : RefScope (RunKnown cx st) e)
    (allocation : AllocationInvariant cx st) :
    AllocationInvariant cx (replaceIfNested cx np owner e depth st).2 := by
  rw [replaceIfNested_group_def]
  simp only [id_bind_eq,allocation_id_pure]
  generalize appView : getAppFnArgs e = pair
  obtain ⟨head,args⟩ := pair
  cases head with
  | const name levels hash =>
    dsimp only [Id.run]
    split
    · exact allocation
    · rename_i notQueued
      have outside : st.typeNames.contains name = false := Bool.eq_false_iff.mpr notQueued
      split
      · rename_i view foundView
        split
        · exact allocation
        · split
          · exact allocation
          · split
            · exact allocation
            · have headEq : (getAppFnArgs e).1 = .const name levels hash := congrArg Prod.fst appView
              have query := expression.externalQuery headEq outside
              have argsScope : ∀ argument ∈ args, RefScope (RunKnown cx st) argument := by
                simpa only [appView] using expression.getAppFnArgs.2
              have specsScope : ∀ argument ∈ (args.extract 0 view.numParams).map (lowerLoose · depth),
                  RefScope (RunKnown cx st) argument := by
                intro argument member
                obtain ⟨original,inExtract,rfl⟩ := Array.mem_map.mp member
                obtain ⟨index,bound,rfl⟩ := Array.mem_extract_iff_getElem.mp inExtract
                exact (argsScope _ (Array.getElem_mem _)).lowerLoose depth 0
              split
              · obtain ⟨roots,state⟩ := allocation
                exact ⟨roots,state.fields rfl rfl rfl rfl⟩
              · split
                · exact allocation
                · dsimp only
                  apply nestedClasses_allocation cx view.numParams owner levels
                    ((args.extract 0 view.numParams).map (lowerLoose · depth))
                    (mkAppN (Expr.mkConst name levels) ((args.extract 0 view.numParams).map (lowerLoose · depth)))
                    _ name _ view st lookup query foundView scope parameters specsScope allocation
      · exact allocation
  | _ => exact allocation

/-- Allocation follows the actual preorder expression traversal. Reference
scope and cache range are reused from their independently checked runtime
theorems; the finite forest is carried through each real recursive call. -/
theorem replaceAll_allocation (cx : XCtx) (np : Nat) (owner : Name)
    (lookup : cx.ind? = IndView.ofConst? cx.source.get?)
    (parameters : ∀ b ∈ cx.paramBinders, BinderScope (RunReach cx) b) :
    ∀ (e : Expr) (depth : Nat) (st : XSt), ExpansionScope cx st → SeenRange st →
      RefScope (RunKnown cx st) e → AllocationInvariant cx st →
      AllocationInvariant cx (replaceAll cx np owner e depth st).2 := by
  intro e
  induction e with
  | app f a hash ihf iha =>
    intro d st scope seen expression allocation
    rw [replaceAll.eq_1]
    have allocated := replaceIfNested_allocation cx np owner (.app f a hash) d st lookup scope parameters expression allocation
    have query := replaceIfNested_scope cx np owner (.app f a hash) d st lookup scope seen parameters expression
    have frame := replaceIfNested_frame cx np owner (.app f a hash) d st
    have cached := replaceIfNested_seenRange cx np owner (.app f a hash) d st seen
    revert allocated query frame cached
    cases replaceIfNested cx np owner (.app f a hash) d st with
    | mk result st1 =>
      intro allocated query frame cached
      cases result with
      | some value => exact allocated
      | none =>
        dsimp only
        have parts : RefScope (RunKnown cx st) f ∧ RefScope (RunKnown cx st) a := by
          simpa [RefScope,sourceExprRefs,or_imp,forall_and] using expression
        have leftScope := parts.1.mono (fun _ known => known.frame frame)
        have first := ihf d st1 query.1 cached leftScope allocated
        have firstScope := replaceAll_scope cx np owner lookup parameters f d st1 query.1 cached leftScope
        have frame1 := replaceAll_frame cx np owner f d st1
        have seen1 := replaceAll_seenRange cx np owner f d st1 cached
        revert first firstScope frame1 seen1
        cases replaceAll cx np owner f d st1 with
        | mk left st2 =>
          intro first firstScope frame1 seen1
          have second := iha d st2 firstScope.1 seen1
            (parts.2.mono (fun _ known => known.frame (frame.trans frame1))) first
          revert second
          cases replaceAll cx np owner a d st2 with
          | mk right st3 => intro second; exact second
  | lam name typ body info hash iht ihb =>
    intro d st scope seen expression allocation
    rw [replaceAll.eq_1]
    have allocated := replaceIfNested_allocation cx np owner (.lam name typ body info hash) d st lookup scope parameters expression allocation
    have query := replaceIfNested_scope cx np owner (.lam name typ body info hash) d st lookup scope seen parameters expression
    have frame := replaceIfNested_frame cx np owner (.lam name typ body info hash) d st
    have cached := replaceIfNested_seenRange cx np owner (.lam name typ body info hash) d st seen
    revert allocated query frame cached
    cases replaceIfNested cx np owner (.lam name typ body info hash) d st with
    | mk result st1 =>
      intro allocated query frame cached
      cases result with
      | some value => exact allocated
      | none =>
        dsimp only
        have parts : RefScope (RunKnown cx st) typ ∧ RefScope (RunKnown cx st) body := by
          simpa [RefScope,sourceExprRefs,or_imp,forall_and] using expression
        have leftScope := parts.1.mono (fun _ known => known.frame frame)
        have first := iht d st1 query.1 cached leftScope allocated
        have firstScope := replaceAll_scope cx np owner lookup parameters typ d st1 query.1 cached leftScope
        have frame1 := replaceAll_frame cx np owner typ d st1
        have seen1 := replaceAll_seenRange cx np owner typ d st1 cached
        revert first firstScope frame1 seen1
        cases replaceAll cx np owner typ d st1 with
        | mk left st2 =>
          intro first firstScope frame1 seen1
          have second := ihb (d+1) st2 firstScope.1 seen1
            (parts.2.mono (fun _ known => known.frame (frame.trans frame1))) first
          revert second
          cases replaceAll cx np owner body (d+1) st2 with
          | mk right st3 => intro second; exact second
  | forallE name typ body info hash iht ihb =>
    intro d st scope seen expression allocation
    rw [replaceAll.eq_1]
    have allocated := replaceIfNested_allocation cx np owner (.forallE name typ body info hash) d st lookup scope parameters expression allocation
    have query := replaceIfNested_scope cx np owner (.forallE name typ body info hash) d st lookup scope seen parameters expression
    have frame := replaceIfNested_frame cx np owner (.forallE name typ body info hash) d st
    have cached := replaceIfNested_seenRange cx np owner (.forallE name typ body info hash) d st seen
    revert allocated query frame cached
    cases replaceIfNested cx np owner (.forallE name typ body info hash) d st with
    | mk result st1 =>
      intro allocated query frame cached
      cases result with
      | some value => exact allocated
      | none =>
        dsimp only
        have parts : RefScope (RunKnown cx st) typ ∧ RefScope (RunKnown cx st) body := by
          simpa [RefScope,sourceExprRefs,or_imp,forall_and] using expression
        have leftScope := parts.1.mono (fun _ known => known.frame frame)
        have first := iht d st1 query.1 cached leftScope allocated
        have firstScope := replaceAll_scope cx np owner lookup parameters typ d st1 query.1 cached leftScope
        have frame1 := replaceAll_frame cx np owner typ d st1
        have seen1 := replaceAll_seenRange cx np owner typ d st1 cached
        revert first firstScope frame1 seen1
        cases replaceAll cx np owner typ d st1 with
        | mk left st2 =>
          intro first firstScope frame1 seen1
          have second := ihb (d+1) st2 firstScope.1 seen1
            (parts.2.mono (fun _ known => known.frame (frame.trans frame1))) first
          revert second
          cases replaceAll cx np owner body (d+1) st2 with
          | mk right st3 => intro second; exact second
  | letE name typ value body nonDep hash iht ihv ihb =>
    intro d st scope seen expression allocation
    rw [replaceAll.eq_1]
    have allocated := replaceIfNested_allocation cx np owner (.letE name typ value body nonDep hash) d st
      lookup scope parameters expression allocation
    have query := replaceIfNested_scope cx np owner (.letE name typ value body nonDep hash) d st
      lookup scope seen parameters expression
    have frame := replaceIfNested_frame cx np owner (.letE name typ value body nonDep hash) d st
    have cached := replaceIfNested_seenRange cx np owner (.letE name typ value body nonDep hash) d st seen
    revert allocated query frame cached
    cases replaceIfNested cx np owner (.letE name typ value body nonDep hash) d st with
    | mk result st1 =>
      intro allocated query frame cached
      cases result with
      | some replacement => exact allocated
      | none =>
        dsimp only
        have parts : RefScope (RunKnown cx st) typ ∧ RefScope (RunKnown cx st) value ∧
            RefScope (RunKnown cx st) body := by
          simpa [RefScope,sourceExprRefs,or_imp,forall_and,and_assoc] using expression
        have typeScope := parts.1.mono (fun _ known => known.frame frame)
        have first := iht d st1 query.1 cached typeScope allocated
        have firstScope := replaceAll_scope cx np owner lookup parameters typ d st1 query.1 cached typeScope
        have frame1 := replaceAll_frame cx np owner typ d st1
        have seen1 := replaceAll_seenRange cx np owner typ d st1 cached
        revert first firstScope frame1 seen1
        cases replaceAll cx np owner typ d st1 with
        | mk typ' st2 =>
          intro first firstScope frame1 seen1
          have valueScope := parts.2.1.mono (fun _ known => known.frame (frame.trans frame1))
          have second := ihv d st2 firstScope.1 seen1 valueScope first
          have secondScope := replaceAll_scope cx np owner lookup parameters value d st2 firstScope.1 seen1 valueScope
          have frame2 := replaceAll_frame cx np owner value d st2
          have seen2 := replaceAll_seenRange cx np owner value d st2 seen1
          revert second secondScope frame2 seen2
          cases replaceAll cx np owner value d st2 with
          | mk value' st3 =>
            intro second secondScope frame2 seen2
            have third := ihb (d+1) st3 secondScope.1 seen2
              (parts.2.2.mono (fun _ known => known.frame (frame.trans (frame1.trans frame2)))) second
            revert third
            cases replaceAll cx np owner body (d+1) st3 with
            | mk body' st4 => intro third; exact third
  | proj name index body hash ih =>
    intro d st scope seen expression allocation
    rw [replaceAll.eq_1]
    have allocated := replaceIfNested_allocation cx np owner (.proj name index body hash) d st lookup scope parameters expression allocation
    have query := replaceIfNested_scope cx np owner (.proj name index body hash) d st lookup scope seen parameters expression
    have frame := replaceIfNested_frame cx np owner (.proj name index body hash) d st
    have cached := replaceIfNested_seenRange cx np owner (.proj name index body hash) d st seen
    revert allocated query frame cached
    cases replaceIfNested cx np owner (.proj name index body hash) d st with
    | mk result st1 =>
      intro allocated query frame cached
      cases result with
      | some value => exact allocated
      | none =>
        dsimp only
        have parts : RunKnown cx st name ∧ RefScope (RunKnown cx st) body := by
          simpa [RefScope,sourceExprRefs,or_imp,forall_and] using expression
        have bodyScope := parts.2
        have next := ih d st1 query.1 cached (bodyScope.mono (fun _ known => known.frame frame)) allocated
        revert next
        cases replaceAll cx np owner body d st1 with
        | mk body' st2 => intro next; exact next
  | mdata data body hash ih =>
    intro d st scope seen expression allocation
    rw [replaceAll.eq_1]
    have allocated := replaceIfNested_allocation cx np owner (.mdata data body hash) d st lookup scope parameters expression allocation
    have query := replaceIfNested_scope cx np owner (.mdata data body hash) d st lookup scope seen parameters expression
    have frame := replaceIfNested_frame cx np owner (.mdata data body hash) d st
    have cached := replaceIfNested_seenRange cx np owner (.mdata data body hash) d st seen
    revert allocated query frame cached
    cases replaceIfNested cx np owner (.mdata data body hash) d st with
    | mk result st1 =>
      intro allocated query frame cached
      cases result with
      | some value => exact allocated
      | none =>
        dsimp only
        have bodyScope : RefScope (RunKnown cx st) body := expression
        have next := ih d st1 query.1 cached (bodyScope.mono (fun _ known => known.frame frame)) allocated
        revert next
        cases replaceAll cx np owner body d st1 with
        | mk body' st2 => intro next; exact next
  | bvar index hash =>
    intro d st scope seen expression allocation
    rw [replaceAll.eq_1]
    have next := replaceIfNested_allocation cx np owner (.bvar index hash) d st lookup scope parameters expression allocation
    revert next
    cases replaceIfNested cx np owner (.bvar index hash) d st with
    | mk result st1 => intro next; cases result <;> exact next
  | fvar name hash =>
    intro d st scope seen expression allocation
    rw [replaceAll.eq_1]
    have next := replaceIfNested_allocation cx np owner (.fvar name hash) d st lookup scope parameters expression allocation
    revert next
    cases replaceIfNested cx np owner (.fvar name hash) d st with
    | mk result st1 => intro next; cases result <;> exact next
  | mvar name hash =>
    intro d st scope seen expression allocation
    rw [replaceAll.eq_1]
    have next := replaceIfNested_allocation cx np owner (.mvar name hash) d st lookup scope parameters expression allocation
    revert next
    cases replaceIfNested cx np owner (.mvar name hash) d st with
    | mk result st1 => intro next; cases result <;> exact next
  | sort level hash =>
    intro d st scope seen expression allocation
    rw [replaceAll.eq_1]
    have next := replaceIfNested_allocation cx np owner (.sort level hash) d st lookup scope parameters expression allocation
    revert next
    cases replaceIfNested cx np owner (.sort level hash) d st with
    | mk result st1 => intro next; cases result <;> exact next
  | const name levels hash =>
    intro d st scope seen expression allocation
    rw [replaceAll.eq_1]
    have next := replaceIfNested_allocation cx np owner (.const name levels hash) d st lookup scope parameters expression allocation
    revert next
    cases replaceIfNested cx np owner (.const name levels hash) d st with
    | mk result st1 => intro next; cases result <;> exact next
  | lit literal hash =>
    intro d st scope seen expression allocation
    rw [replaceAll.eq_1]
    have next := replaceIfNested_allocation cx np owner (.lit literal hash) d st lookup scope parameters expression allocation
    revert next
    cases replaceIfNested cx np owner (.lit literal hash) d st with
    | mk result st1 => intro next; cases result <;> exact next


/-- Rewriting the selected constructor changes only its payload after the
actual expression walk has finished allocating. -/
theorem walkCtor_allocation (cx : XCtx) (qi ci : Nat) (st : XSt)
    (lookup : cx.ind? = IndView.ofConst? cx.source.get?)
    (parameters : ∀ b ∈ cx.paramBinders, BinderScope (RunReach cx) b)
    (scope : ExpansionScope cx st) (seen : SeenRange st)
    (allocation : AllocationInvariant cx st) :
    AllocationInvariant cx (walkCtor cx qi ci st) := by
  unfold walkCtor
  split
  · exact allocation
  · rename_i member foundMember
    split
    · exact allocation
    · rename_i ctor foundCtor
      have constructorScope := (scope.members member (Array.mem_of_getElem? foundMember)).2
        ctor (Array.mem_of_getElem? foundCtor)
      have peeled := constructorScope.peelForalls cx.nParams #[] (by simp)
      generalize telescope : peelForalls cx.nParams ctor.typ #[] = pair at peeled ⊢
      obtain ⟨binders,body⟩ := pair
      dsimp only at peeled ⊢
      have allocated := replaceAll_allocation cx binders.size member.sourceOwner
        lookup parameters body 0 st scope seen peeled.1 allocation
      revert allocated
      cases replaceAll cx binders.size member.sourceOwner body 0 st with
      | mk body' next =>
        intro allocated
        obtain ⟨roots,state⟩ := allocated
        exact ⟨roots,state.fields rfl rfl rfl rfl⟩

/-- The actual queue preserves the allocation forest, keeping every error
and fuel branch of the executable queue unchanged. -/
theorem walkQueue_allocation (cx : XCtx)
    (lookup : cx.ind? = IndView.ofConst? cx.source.get?)
    (parameters : ∀ b ∈ cx.paramBinders, BinderScope (RunReach cx) b) :
    ∀ (fuel qi : Nat) (st final : XSt), ExpansionScope cx st → SeenRange st →
      AllocationInvariant cx st → walkQueue cx fuel qi st = .ok final →
      AllocationInvariant cx final
  | 0,qi,st,final,scope,seen,allocation,run => by
    rw [walkQueue.eq_1] at run
    split at run
    · cases run
    · split at run
      · cases run
      · cases except_pure_ok run
        exact allocation
  | fuel+1,qi,st,final,scope,seen,allocation,run => by
    rw [walkQueue.eq_2] at run
    split at run
    · cases run
    · split at run
      · cases except_pure_ok run
        exact allocation
      · rename_i member found
        have step :
            let next := (List.range member.ctors.size).foldl (fun s ci => walkCtor cx qi ci s) st
            ExpansionScope cx next ∧ SeenRange next ∧ AllocationInvariant cx next := by
          dsimp only
          refine list_foldl_inv (fun s =>
            ExpansionScope cx s ∧ SeenRange s ∧ AllocationInvariant cx s)
            _ ?_ _ _ ⟨scope,seen,allocation⟩
          intro current index invariant
          exact ⟨walkCtor_scope cx qi index current lookup parameters invariant.1 invariant.2.1,
            walkCtor_seenRange cx qi index current invariant.2.1,
            walkCtor_allocation cx qi index current lookup parameters invariant.1 invariant.2.1 invariant.2.2⟩
        exact walkQueue_allocation cx lookup parameters fuel (qi+1) _ final
          step.1 step.2.1 step.2.2 run

/-- Original members do not reserve auxiliary or constructor families. -/
theorem initialMembers_allocation {cx : XCtx} (ordered : Array Name)
    (aliases : Std.HashMap Name Name) {st : XSt}
    (run : initialMembers cx ordered aliases = .ok st) : AllocationState cx [] st := by
  unfold initialMembers at run
  apply forIn_except_array_mem _ (fun _ state => AllocationState cx [] state) ordered
    ?_ (AllocationState.empty cx) run
  intro pre name before step member allocation result
  split at result
  · cases except_pure_ok result
    exact ⟨_,rfl,allocation.fields rfl rfl rfl rfl⟩
  · cases result

/-- Every successful canonical expansion has the finite allocation forest
of its actual final queue. All source, ownership and scope facts come from
the real initializer and the actual queue transitions. -/
theorem expand_allocationInvariant (source : Ix.Environment) (dedup : Dedup)
    (classes : Array (Array Name)) (groupOf : SourceGroups)
    (keyAddr? : Option (Name → Option Address)) {x : Expanded}
    (run : expandSourceSpec source dedup (repsOf classes) (aliasesOf classes) groupOf keyAddr? = .ok x) :
    ∃ (first : Name) (fi : IndView),
      (repsOf classes)[0]? = some first ∧ IndView.ofConst? source.get? first = some fi ∧
      let cx : XCtx := {
        source, sourceMembers := repsOf classes, ind? := IndView.ofConst? source.get?,
        groupOf, keyAddr?, dedup, all0 := fi.all[0]?.getD first,
        blockLevels := fi.levelParams.map Ix.Level.mkParam,
        levelParams := fi.levelParams.toList, nParams := fi.numParams,
        paramBinders := (peelForalls fi.numParams fi.type #[]).1 }
      ∃ initial final,
        initialMembers cx (repsOf classes) (aliasesOf classes) = .ok initial ∧
        walkQueue cx expansionBound 0 initial = .ok final ∧
        AllocationInvariant cx final ∧
        x = {
          types := final.types, auxToNested := final.auxToNested,
          auxCtorMap := final.auxCtorMap, nOriginals := initial.types.size,
          levelParams := fi.levelParams, nParams := fi.numParams,
          all0 := cx.all0, sourceNames := final.sourceNames?.getD [] } := by
  obtain ⟨first,fi,firstFound,viewFound,initial,final,initialRun,scope,parameters,queueRun,output⟩ :=
    expand_initialization source dedup classes groupOf keyAddr? run
  refine ⟨first,fi,firstFound,viewFound,initial,final,initialRun,queueRun,?_,output⟩
  have seen : SeenRange initial := by
    intro key value member
    rw [initialMembers_seen (repsOf classes) (aliasesOf classes) initialRun] at member
    cases member
  exact walkQueue_allocation _ rfl parameters expansionBound 0 initial final scope seen
    ⟨[],initialMembers_allocation (repsOf classes) (aliasesOf classes) initialRun⟩ queueRun

/-- The actual output origin tables index a finite, separated allocation
forest. This follows from the real run, without a caller freshness premise. -/
theorem expand_originForest (source : Ix.Environment) (dedup : Dedup)
    (classes : Array (Array Name)) (groupOf : SourceGroups)
    (keyAddr? : Option (Name → Option Address)) {x : Expanded}
    (run : expandSourceSpec source dedup (repsOf classes) (aliasesOf classes) groupOf keyAddr? = .ok x) :
    AllocationForest (keyName (Name.mkStr x.all0 "_nested"))
      (x.auxToNested.entries.map (fun entry => keyName entry.1))
      (x.auxCtorMap.entries.map (fun entry => keyName entry.1)) := by
  obtain ⟨first,fi,firstFound,viewFound,initial,final,initialRun,queueRun,
    ⟨roots,allocation⟩,output⟩ :=
    expand_allocationInvariant source dedup classes groupOf keyAddr? run
  cases output
  simpa only [allocation.rootKeys,allocation.ctorKeys] using allocation.forest

/-- Every output auxiliary and constructor family is disjoint from the
actual block-reachable source spellings, including all protected metadata. -/
theorem expand_originSourceFree (source : Ix.Environment) (dedup : Dedup)
    (classes : Array (Array Name)) (groupOf : SourceGroups)
    (keyAddr? : Option (Name → Option Address)) {x : Expanded}
    (run : expandSourceSpec source dedup (repsOf classes) (aliasesOf classes) groupOf keyAddr? = .ok x) :
    (∀ entry ∈ x.auxToNested.entries, ∀ original ∈
      (sourceContext source (repsOf classes) groupOf.blocks).protectedNames,
        (keyName entry.1).isPrefixOf original = false) ∧
    (∀ entry ∈ x.auxCtorMap.entries, ∀ original ∈
      (sourceContext source (repsOf classes) groupOf.blocks).protectedNames,
        (keyName entry.1).isPrefixOf original = false) := by
  obtain ⟨first,fi,firstFound,viewFound,initial,final,initialRun,queueRun,
    ⟨roots,allocation⟩,output⟩ :=
    expand_allocationInvariant source dedup classes groupOf keyAddr? run
  cases output
  constructor
  · intro entry member original protectedName
    apply allocation.sourceFree (keyName entry.1) ?_ original protectedName
    apply allocation.rootsCover
    rw [← allocation.rootKeys]
    exact List.mem_map.mpr ⟨entry,member,rfl⟩
  · intro entry member original protectedName
    apply allocation.sourceFree (keyName entry.1) ?_ original protectedName
    apply allocation.ctorsCover
    rw [← allocation.ctorKeys]
    exact List.mem_map.mpr ⟨entry,member,rfl⟩

/-- The output tables retain the full bidirectional constructor-versus-
reserved-suffix-family separation established by the actual allocation run. -/
theorem expand_originSuffixApart (source : Ix.Environment) (dedup : Dedup)
    (classes : Array (Array Name)) (groupOf : SourceGroups)
    (keyAddr? : Option (Name → Option Address)) {x : Expanded}
    (run : expandSourceSpec source dedup (repsOf classes) (aliasesOf classes) groupOf keyAddr? = .ok x) :
    ∀ ctor ∈ x.auxCtorMap.entries, ∀ aux ∈ x.auxToNested.entries,
      ∀ suffix ∈ auxSuffixFamilies aux.1, Apart (keyName ctor.1) suffix := by
  obtain ⟨first,fi,firstFound,viewFound,initial,final,initialRun,queueRun,
    ⟨roots,allocation⟩,output⟩ :=
    expand_allocationInvariant source dedup classes groupOf keyAddr? run
  cases output
  intro ctor ctorMember aux auxMember suffix suffixMember
  apply allocation.suffixFree (keyName ctor.1) ?_ aux.1 ?_ suffix suffixMember
  · rw [← allocation.ctorKeys]
    exact List.mem_map.mpr ⟨ctor,ctorMember,rfl⟩
  · rw [← allocation.rootKeys]
    exact List.mem_map.mpr ⟨aux,auxMember,rfl⟩

end Ix.CompileCert.Canon
