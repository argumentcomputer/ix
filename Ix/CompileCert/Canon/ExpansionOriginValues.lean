import Ix.CompileCert.Canon.ExpansionQueue

namespace Ix.CompileCert.Canon
open Ix.Compile.Canon
open Ix (Name Expr)

/-- An absent structural insertion preserves every previous successful
lookup, including queries with different cached hashes. -/
theorem nameTable_insert_absent_preserves {α : Type} (table : NameTable α)
    (fresh query : Name) (value previous : α)
    (absent : table.get? fresh = none) (found : table.get? query = some previous) :
    (table.insert fresh value).get? query = some previous := by
  rw [NameTable.get?_insert]
  split
  · rename_i same
    have equal : table.get? fresh = table.get? query := by
      unfold NameTable.get?
      rw [same]
    rw [equal,found] at absent
    cases absent
  · exact found

/-- The exact allocator candidate is absent from the actual constructor
origin table, with no independent key/freshness premise. -/
theorem AllocationState.ctorCandidate_absent {cx : XCtx} {roots : List Lean.Name} {st : XSt}
    (allocation : AllocationState cx roots st) (aux candidate : Name) (index : Nat) :
    st.auxCtorMap.get?
      (freshCtorFamily (st.allocatedNames ++
        (sourceContext cx.source cx.sourceMembers cx.groupOf.blocks).protectedNames)
        aux candidate index st.allocatedCtorRoots) = none := by
  apply nameTable_absent_of_familyFree st.auxCtorMap _ (st.allocatedNames ++
    (sourceContext cx.source cx.sourceMembers cx.groupOf.blocks).protectedNames)
  · intro name value member
    apply List.mem_append_left
    apply allocation.ctorsCover
    rw [← allocation.ctorKeys]
    exact List.mem_map.mpr ⟨(name,value),member,rfl⟩
  · exact freshCtorFamily_free _ _ _ _ _

/-- Every constructor emitted by the real constructor loop retains an exact
source-constructor/auxiliary-owner lookup. Later fresh insertions preserve
prior lookups; the original constructor spelling need not be prefixed by its
inductive. The enclosing actual class proof supplies source protection. -/
theorem nestedCtors_originValues (cx : XCtx) (sourceName auxName : Name) (view : IndView)
    (externalParams : Nat) (levels : Array Ix.Level) (specs : Array Expr)
    (sourceNames : List Lean.Name) (st : XSt) (roots : List Lean.Name)
    (sameSources : sourceNames =
      (sourceContext cx.source cx.sourceMembers cx.groupOf.blocks).protectedNames)
    (allocation : AllocationState cx roots st) (owned : keyName auxName ∈ roots)
    (protectedCtors : ∀ ctor ∈ view.ctors, keyName ctor.1 ∈ sourceNames) :
    let result := nestedCtors cx sourceName auxName view externalParams levels specs sourceNames st
    ∀ generated ∈ result.2, ∃ original ∈ view.ctors,
      result.1.auxCtorMap.get? generated.name = some (original.1,auxName) := by
  subst sourceNames
  have all :
      let result := nestedCtors cx sourceName auxName view externalParams levels specs
        (sourceContext cx.source cx.sourceMembers cx.groupOf.blocks).protectedNames st
      AllocationState cx roots result.1 ∧
        ∀ generated ∈ result.2, ∃ original ∈ view.ctors,
          result.1.auxCtorMap.get? generated.name = some (original.1,auxName) := by
    unfold nestedCtors
    refine forIn_id_inv_array_mem (fun q : XSt × Array XCtor =>
      AllocationState cx roots q.1 ∧ ∀ generated ∈ q.2,
        ∃ original ∈ view.ctors, q.1.auxCtorMap.get? generated.name = some (original.1,auxName))
      _ _ _ ⟨allocation,by simp⟩ ?_
    intro sourceCtor sourceMember q previous
    obtain ⟨cn,ct,nf⟩ := sourceCtor
    have allocated := previous.1.constructor auxName cn sourceName q.2.size owned
      (protectedCtors (cn,ct,nf) sourceMember)
    have absent := previous.1.ctorCandidate_absent auxName
      (nameReplacePrefix cn sourceName auxName) q.2.size
    refine ⟨allocated.fields rfl rfl rfl rfl,?_⟩
    intro generated member
    change generated ∈ q.2.push _ at member
    rcases Array.mem_push.mp member with old | rfl
    · obtain ⟨original,inSource,found⟩ := previous.2 generated old
      exact ⟨original,inSource,nameTable_insert_absent_preserves q.1.auxCtorMap _ generated.name
        (cn,auxName) (original.1,auxName) absent found⟩
    · exact ⟨(cn,ct,nf),sourceMember,NameTable.get?_insert_self q.1.auxCtorMap _ (cn,auxName)⟩
  exact all.2

/-- Every existing successful structural-name lookup retains its exact value. -/
def NameTablePreserves {α : Type} (before after : NameTable α) : Prop :=
  ∀ name value, before.get? name = some value → after.get? name = some value

theorem NameTablePreserves.refl {α : Type} (table : NameTable α) :
    NameTablePreserves table table := fun _ _ found => found

theorem NameTablePreserves.trans {α : Type} {before middle after : NameTable α}
    (first : NameTablePreserves before middle) (second : NameTablePreserves middle after) :
    NameTablePreserves before after := fun name value found => second name value (first name value found)

/-- Cache fields are irrelevant: the exact entry list supplies the lookup. -/
theorem NameTablePreserves.entries {α : Type} {before after : NameTable α}
    (same : after.entries = before.entries) : NameTablePreserves before after := by
  intro name value found
  simpa only [NameTable.get?,same] using found

/-- Both generated-origin maps extend their previous successful lookups. -/
structure OriginTablesExtend (before after : XSt) : Prop where
  auxiliaries : NameTablePreserves before.auxToNested after.auxToNested
  constructors : NameTablePreserves before.auxCtorMap after.auxCtorMap

theorem OriginTablesExtend.refl (st : XSt) : OriginTablesExtend st st :=
  ⟨NameTablePreserves.refl _,NameTablePreserves.refl _⟩

theorem OriginTablesExtend.trans {before middle after : XSt}
    (first : OriginTablesExtend before middle) (second : OriginTablesExtend middle after) :
    OriginTablesExtend before after :=
  ⟨first.auxiliaries.trans second.auxiliaries,first.constructors.trans second.constructors⟩

theorem OriginTablesExtend.fields {before after : XSt}
    (auxiliaries : after.auxToNested.entries = before.auxToNested.entries)
    (constructors : after.auxCtorMap.entries = before.auxCtorMap.entries) :
    OriginTablesExtend before after :=
  ⟨NameTablePreserves.entries auxiliaries,NameTablePreserves.entries constructors⟩

/-- Actual auxiliary-family allocation is fresh for the current origin map. -/
theorem AllocationState.auxCandidate_absent {cx : XCtx} {roots : List Lean.Name} {st : XSt}
    (allocation : AllocationState cx roots st) (label : String) :
    st.auxToNested.get?
      (freshFamily (st.allocatedNames ++
        (sourceContext cx.source cx.sourceMembers cx.groupOf.blocks).protectedNames)
        (Name.mkStr cx.all0 "_nested") label) = none := by
  apply nameTable_absent_of_familyFree st.auxToNested _ (st.allocatedNames ++
    (sourceContext cx.source cx.sourceMembers cx.groupOf.blocks).protectedNames)
  · intro name value member
    apply List.mem_append_left
    apply allocation.rootsCover
    rw [← allocation.rootKeys]
    exact List.mem_map.mpr ⟨(name,value),member,rfl⟩
  · exact freshFamily_free _ _ _

/-- The actual constructor loop preserves every older origin value while
it inserts the newly allocated constructor records. -/
theorem nestedCtors_originTablesExtend (cx : XCtx) (sourceName auxName : Name) (view : IndView)
    (externalParams : Nat) (levels : Array Ix.Level) (specs : Array Expr)
    (sourceNames : List Lean.Name) (st : XSt) (roots : List Lean.Name)
    (sameSources : sourceNames =
      (sourceContext cx.source cx.sourceMembers cx.groupOf.blocks).protectedNames)
    (allocation : AllocationState cx roots st) (owned : keyName auxName ∈ roots)
    (protectedCtors : ∀ ctor ∈ view.ctors, keyName ctor.1 ∈ sourceNames) :
    OriginTablesExtend st
      (nestedCtors cx sourceName auxName view externalParams levels specs sourceNames st).1 := by
  have history := nestedCtors_originHistory cx sourceName auxName view externalParams levels specs sourceNames st
  refine ⟨NameTablePreserves.entries history.1,?_⟩
  subst sourceNames
  have all :
      let result := nestedCtors cx sourceName auxName view externalParams levels specs
        (sourceContext cx.source cx.sourceMembers cx.groupOf.blocks).protectedNames st
      AllocationState cx roots result.1 ∧ NameTablePreserves st.auxCtorMap result.1.auxCtorMap := by
    unfold nestedCtors
    refine forIn_id_inv_array_mem (fun q : XSt × Array XCtor =>
      AllocationState cx roots q.1 ∧ NameTablePreserves st.auxCtorMap q.1.auxCtorMap)
      _ _ _ ⟨allocation,NameTablePreserves.refl _⟩ ?_
    intro sourceCtor sourceMember q previous
    obtain ⟨cn,ct,nf⟩ := sourceCtor
    have allocated := previous.1.constructor auxName cn sourceName q.2.size owned
      (protectedCtors (cn,ct,nf) sourceMember)
    have absent := previous.1.ctorCandidate_absent auxName
      (nameReplacePrefix cn sourceName auxName) q.2.size
    refine ⟨allocated.fields rfl rfl rfl rfl,?_⟩
    intro query value found
    exact nameTable_insert_absent_preserves q.1.auxCtorMap _ query (cn,auxName) value absent
      (previous.2 query value found)
  exact all.2

/-- One actual class step preserves all earlier origin values, across both
cache policies and the skipped-class branches. Source protection is derived
from the existing internal scope/reachability invariant. -/
theorem nestedClassStep_originTablesExtend (cx : XCtx) (owner : Name) (externalParams : Nat)
    (levels : Array Ix.Level) (specs : Array Expr) (original : Expr)
    (keyOf : Expr → Except String OccurrenceInput) (head : Name)
    (repl : Name → Expr) (cls : Array Name) (state next : XSt × Option Expr)
    (lookup : cx.ind? = IndView.ofConst? cx.source.get?)
    (scope : ExpansionScope cx state.1) (roots : List Lean.Name)
    (allocation : AllocationState cx roots state.1)
    (reached : ∀ name ∈ cls, RunReach cx name)
    (run : nestedClassStep cx owner externalParams levels specs original keyOf head repl cls state =
      .yield next) : OriginTablesExtend state.1 next.1 := by
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
      have absent : state.1.auxToNested.get? auxName = none := by
        have fresh := allocation.auxCandidate_absent
          s!"{(namePretty name).replace "." "_"}_{state.1.nextAuxIdx}"
        rw [← scope.sourceNames] at fresh
        exact fresh
      have preparedExtend : OriginTablesExtend state.1 prepared := by
        constructor
        · intro query value previous
          exact nameTable_insert_absent_preserves state.1.auxToNested auxName query _ value absent previous
        · exact NameTablePreserves.refl _
      have preparedAllocation : AllocationState cx (keyName auxName :: roots) prepared := by
        have reserve := allocation.reserve s!"{(namePretty name).replace "." "_"}_{state.1.nextAuxIdx}"
          (mkAppN (Expr.mkConst name levels) specs)
        dsimp only at reserve
        rw [← scope.sourceNames] at reserve
        exact reserve.fields rfl rfl rfl rfl
      have cacheFields := nestedSeen_allocations cx.dedup original
        (fun alias => keyOf (mkAppN (Expr.mkConst alias levels) specs)) cls auxName prepared
      have registeredAllocation : AllocationState cx (keyName auxName :: roots) registered :=
        preparedAllocation.fields cacheFields.1 cacheFields.2.1 cacheFields.2.2.1 cacheFields.2.2.2
      have registeredExtend : OriginTablesExtend prepared registered :=
        OriginTablesExtend.fields cacheFields.2.2.1 cacheFields.2.2.2
      have actual : IndView.ofConst? cx.source.get? name = some view := by simpa [lookup] using found
      have nameReached := reached name (Array.mem_of_getElem? chosen)
      have ctorExtend : OriginTablesExtend registered result.1 := by
        apply nestedCtors_originTablesExtend cx name auxName view externalParams levels specs sourceNames
          registered (keyName auxName :: roots) scope.sourceNames registeredAllocation List.mem_cons_self
        intro ctor inView
        rw [show sourceNames =
          (sourceContext cx.source cx.sourceMembers cx.groupOf.blocks).protectedNames from scope.sourceNames]
        exact (nameReached.viewCtor actual inView).2.2
      exact (preparedExtend.trans (registeredExtend.trans ctorExtend)).trans
        (OriginTablesExtend.fields rfl rfl)
    · cases run
      exact OriginTablesExtend.refl _
  · cases run
    exact OriginTablesExtend.refl _

/-- A generated member's actual source occurrence and constructor origins.
The witnesses are read from the real source lookup and the two origin maps;
this is an internal queue invariant, not a premise on compiler inputs. -/
def MemberOrigin (cx : XCtx) (st : XSt) (member : XMember) : Prop :=
  ∃ (sourceName : Name) (view : IndView) (levels : Array Ix.Level) (specs : Array Expr),
    cx.ind? sourceName = some view ∧
    st.auxToNested.get? member.name = some (mkAppN (Expr.mkConst sourceName levels) specs) ∧
    ∀ generated ∈ member.ctors, ∃ original ∈ view.ctors,
      st.auxCtorMap.get? generated.name = some (original.1,member.name)

/-- Extending both origin tables retains the complete source witness. -/
theorem MemberOrigin.extend {cx : XCtx} {before after : XSt} {member : XMember}
    (origin : MemberOrigin cx before member) (extension : OriginTablesExtend before after) :
    MemberOrigin cx after member := by
  obtain ⟨name,view,levels,specs,found,auxiliary,constructors⟩ := origin
  refine ⟨name,view,levels,specs,found,extension.auxiliaries _ _ auxiliary,?_⟩
  intro generated member
  obtain ⟨original,inView,stored⟩ := constructors generated member
  exact ⟨original,inView,extension.constructors _ _ stored⟩

/-- Changes to constructor types retain source origins when the actual
member and constructor names are retained. No source constructor prefix
condition is used. -/
theorem MemberOrigin.fields {cx : XCtx} {st : XSt} {before after : XMember}
    (origin : MemberOrigin cx st before) (sameName : after.name = before.name)
    (constructors : ∀ generated ∈ after.ctors, ∃ previous ∈ before.ctors,
      previous.name = generated.name) : MemberOrigin cx st after := by
  obtain ⟨name,view,levels,specs,found,auxiliary,storedCtors⟩ := origin
  refine ⟨name,view,levels,specs,found,?_,?_⟩
  · simpa only [sameName] using auxiliary
  · intro generated member
    obtain ⟨previous,inBefore,sameCtor⟩ := constructors generated member
    obtain ⟨original,inView,stored⟩ := storedCtors previous inBefore
    refine ⟨original,inView,?_⟩
    simpa only [← sameCtor,sameName] using stored

/-- The real class body appends at most one member. Every appended member
has its exact source lookup/occurrence and every emitted constructor has its
exact source constructor plus auxiliary owner. Existing members are retained
literally. The skipped-class and skipped-view cases append nothing. -/
theorem nestedClassStep_createdOrigins (cx : XCtx) (owner : Name) (externalParams : Nat)
    (levels : Array Ix.Level) (specs : Array Expr) (original : Expr)
    (keyOf : Expr → Except String OccurrenceInput) (head : Name)
    (repl : Name → Expr) (cls : Array Name) (state next : XSt × Option Expr)
    (lookup : cx.ind? = IndView.ofConst? cx.source.get?)
    (scope : ExpansionScope cx state.1) (roots : List Lean.Name)
    (allocation : AllocationState cx roots state.1)
    (reached : ∀ name ∈ cls, RunReach cx name)
    (run : nestedClassStep cx owner externalParams levels specs original keyOf head repl cls state =
      .yield next) :
    ∃ appended : List XMember,
      next.1.types.toList = state.1.types.toList ++ appended ∧ appended.length ≤ 1 ∧
      ∀ member ∈ appended, member.sourceOwner = owner ∧ MemberOrigin cx next.1 member := by
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
      have preparedAllocation : AllocationState cx (keyName auxName :: roots) prepared := by
        have reserve := allocation.reserve s!"{(namePretty name).replace "." "_"}_{state.1.nextAuxIdx}"
          (mkAppN (Expr.mkConst name levels) specs)
        dsimp only at reserve
        rw [← scope.sourceNames] at reserve
        exact reserve.fields rfl rfl rfl rfl
      have cacheFields := nestedSeen_fields cx.dedup original
        (fun alias => keyOf (mkAppN (Expr.mkConst alias levels) specs)) cls auxName prepared
      have cacheAllocation := nestedSeen_allocations cx.dedup original
        (fun alias => keyOf (mkAppN (Expr.mkConst alias levels) specs)) cls auxName prepared
      have registeredAllocation : AllocationState cx (keyName auxName :: roots) registered :=
        preparedAllocation.fields cacheAllocation.1 cacheAllocation.2.1
          cacheAllocation.2.2.1 cacheAllocation.2.2.2
      have actual : IndView.ofConst? cx.source.get? name = some view := by simpa [lookup] using found
      have nameReached := reached name (Array.mem_of_getElem? chosen)
      have ctorValues : ∀ generated ∈ result.2, ∃ original ∈ view.ctors,
          result.1.auxCtorMap.get? generated.name = some (original.1,auxName) := by
        apply nestedCtors_originValues cx name auxName view externalParams levels specs sourceNames
          registered (keyName auxName :: roots) scope.sourceNames registeredAllocation List.mem_cons_self
        intro ctor inView
        rw [show sourceNames =
          (sourceContext cx.source cx.sourceMembers cx.groupOf.blocks).protectedNames from scope.sourceNames]
        exact (nameReached.viewCtor actual inView).2.2
      have ctorFields := nestedCtors_fields cx name auxName view externalParams levels specs sourceNames registered
      have history := nestedCtors_originHistory cx name auxName view externalParams levels specs sourceNames registered
      have auxiliary : result.1.auxToNested.get? auxName =
          some (mkAppN (Expr.mkConst name levels) specs) := by
        unfold NameTable.get?
        rw [history.1,cacheAllocation.2.2.1]
        exact NameTable.get?_insert_self state.1.auxToNested auxName _
      have origin : MemberOrigin cx (result.1.push member) member :=
        ⟨name,view,levels,specs,found,auxiliary,ctorValues⟩
      refine ⟨[member],?_,by simp,?_⟩
      · change (result.1.types.push member).toList = _
        rw [Array.toList_push,ctorFields.1,cacheFields.1]
      · intro emitted inNew
        have same : emitted = member := by simpa using inNew
        subst emitted
        exact ⟨rfl,origin⟩
    · cases run
      exact ⟨[],by simp,by simp,by simp⟩
  · cases run
    exact ⟨[],by simp,by simp,by simp⟩

/-- Every queued auxiliary after the fixed original prefix has its actual
source occurrence and constructor-origin values in the current maps. -/
structure QueueOriginValues (cx : XCtx) (nOriginals : Nat) (st : XSt) : Prop where
  originalBound : nOriginals ≤ st.types.size
  members : ∀ member ∈ st.types.toList.drop nOriginals, MemberOrigin cx st member

/-- The actual original prefix initially contains no generated auxiliary. -/
theorem QueueOriginValues.initial (cx : XCtx) (st : XSt) :
    QueueOriginValues cx st.types.size st := by
  constructor
  · exact Nat.le_refl _
  · intro member present
    have length : st.types.toList.length = st.types.size := by simp
    rw [← length,List.drop_length] at present
    cases present

/-- An unchanged queue and extended origin maps retain every source witness. -/
theorem QueueOriginValues.fields {cx : XCtx} {n : Nat} {before after : XSt}
    (queue : QueueOriginValues cx n before) (types : after.types = before.types)
    (extension : OriginTablesExtend before after) : QueueOriginValues cx n after := by
  constructor
  · simpa only [types] using queue.originalBound
  · intro member present
    have old := queue.members member (by simpa only [types] using present)
    exact old.extend extension

/-- The exact class step retains old witnesses and supplies the newly
appended member's witness, with no premise about its generated spelling. -/
theorem nestedClassStep_queueOriginValues (cx : XCtx) (owner : Name) (externalParams : Nat)
    (levels : Array Ix.Level) (specs : Array Expr) (original : Expr)
    (keyOf : Expr → Except String OccurrenceInput) (head : Name)
    (repl : Name → Expr) (cls : Array Name) (state next : XSt × Option Expr)
    (lookup : cx.ind? = IndView.ofConst? cx.source.get?)
    (scope : ExpansionScope cx state.1) (roots : List Lean.Name)
    (allocation : AllocationState cx roots state.1)
    (reached : ∀ name ∈ cls, RunReach cx name)
    (n : Nat) (queue : QueueOriginValues cx n state.1)
    (run : nestedClassStep cx owner externalParams levels specs original keyOf head repl cls state =
      .yield next) : QueueOriginValues cx n next.1 := by
  have extension := nestedClassStep_originTablesExtend cx owner externalParams levels specs original
    keyOf head repl cls state next lookup scope roots allocation reached run
  obtain ⟨appended,types,_,created⟩ := nestedClassStep_createdOrigins cx owner externalParams levels specs original
    keyOf head repl cls state next lookup scope roots allocation reached run
  constructor
  · have sizes : next.1.types.size = state.1.types.size + appended.length := by
      simpa only [List.length_append,Array.length_toList] using congrArg List.length types
    have bound := queue.originalBound
    omega
  · intro member present
    have bound : n ≤ state.1.types.toList.length := by simpa using queue.originalBound
    rw [types,drop_append_prefix _ _ _ bound] at present
    rcases List.mem_append.mp present with old | added
    · exact (queue.members member old).extend extension
    · exact (created member added).2

/-- The actual class loop carries the fixed original prefix and complete
source-origin witnesses through every class, including skipped classes. Its scope
and allocation facts are internal invariants from the real query. -/
theorem nestedClasses_queueOriginValues (cx : XCtx) (np : Nat) (owner : Name)
    (levels : Array Ix.Level) (specs : Array Expr) (original : Expr)
    (keyOf : Expr → Except String OccurrenceInput) (head : Name)
    (repl : Name → Expr) (view : IndView) (st : XSt)
    (lookup : cx.ind? = IndView.ofConst? cx.source.get?)
    (query : RunReach cx head) (found : cx.ind? head = some view)
    (scope : ExpansionScope cx st)
    (parameters : ∀ b ∈ cx.paramBinders, BinderScope (RunReach cx) b)
    (arguments : ∀ e ∈ specs, RefScope (RunKnown cx st) e)
    (allocation : AllocationInvariant cx st) (n : Nat) (queue : QueueOriginValues cx n st) :
    QueueOriginValues cx n
      (forIn (m := Id) (cx.groupOf view) (st,none)
        (nestedClassStep cx owner np levels specs original keyOf head repl)).1 := by
  have all :
      let result := forIn (m := Id) (cx.groupOf view) (st,none)
        (nestedClassStep cx owner np levels specs original keyOf head repl)
      ExpansionScope cx result.1 ∧ ExpansionFrame cx st result.1 ∧
        AllocationInvariant cx result.1 ∧ QueueOriginValues cx n result.1 := by
    dsimp only
    refine forIn_id_inv_array_mem (fun state : XSt × Option Expr =>
      ExpansionScope cx state.1 ∧ ExpansionFrame cx st state.1 ∧
        AllocationInvariant cx state.1 ∧ QueueOriginValues cx n state.1)
      _ _ _ ⟨scope,ExpansionFrame.refl cx st,allocation,queue⟩ ?_
    intro cls member state invariant
    obtain ⟨next,step⟩ := nestedClassStep_yield cx owner np levels specs original keyOf head repl cls state
    rw [step]
    have reached : ∀ name ∈ cls, RunReach cx name := by
      intro name inClass
      apply query.groupMember (groups := cx.groupOf) ?_ member inClass
      simpa [lookup] using found
    have stepFrame := nestedClassStep_frame cx owner np levels specs original keyOf head repl cls state next step
    obtain ⟨roots,allocated⟩ := invariant.2.2.1
    refine ⟨nestedClassStep_expansionScope cx owner np levels specs original keyOf head repl cls state next
      lookup invariant.1 parameters ?_ reached step,
      invariant.2.1.trans stepFrame,
      nestedClassStep_allocation cx owner np levels specs original keyOf head repl cls state next
        lookup invariant.1 roots allocated reached step,
      nestedClassStep_queueOriginValues cx owner np levels specs original keyOf head repl cls state next
        lookup invariant.1 roots allocated reached n invariant.2.2.2 step⟩
    intro e inSpecs
    exact (arguments e inSpecs).mono (fun _ known => known.frame invariant.2.1)
  exact all.2.2.2

private theorem queueOriginValues_id_pure {α : Type} (value : α) : (pure value : Id α) = value := rfl

/-- Every actual query branch preserves queue source-origin values. The error
branch changes only the pending error; hits and ineligible expressions retain
state, and the miss branch is the actual complete class loop. -/
theorem replaceIfNested_queueOriginValues (cx : XCtx) (np : Nat) (owner : Name)
    (e : Expr) (depth : Nat) (st : XSt)
    (lookup : cx.ind? = IndView.ofConst? cx.source.get?)
    (scope : ExpansionScope cx st)
    (parameters : ∀ b ∈ cx.paramBinders, BinderScope (RunReach cx) b)
    (expression : RefScope (RunKnown cx st) e)
    (allocation : AllocationInvariant cx st) (n : Nat) (queue : QueueOriginValues cx n st) :
    QueueOriginValues cx n (replaceIfNested cx np owner e depth st).2 := by
  rw [replaceIfNested_group_def]
  simp only [id_bind_eq,queueOriginValues_id_pure]
  generalize appView : getAppFnArgs e = pair
  obtain ⟨head,args⟩ := pair
  cases head with
  | const name levels hash =>
    dsimp only [Id.run]
    split
    · exact queue
    · rename_i notQueued
      have outside : st.typeNames.contains name = false := Bool.eq_false_iff.mpr notQueued
      split
      · rename_i view foundView
        split
        · exact queue
        · split
          · exact queue
          · split
            · exact queue
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
              · exact queue.fields rfl (OriginTablesExtend.fields rfl rfl)
              · split
                · exact queue
                · dsimp only
                  exact nestedClasses_queueOriginValues cx view.numParams owner levels
                    ((args.extract 0 view.numParams).map (lowerLoose · depth))
                    (mkAppN (Expr.mkConst name levels) ((args.extract 0 view.numParams).map (lowerLoose · depth)))
                    _ name _ view st lookup query foundView scope parameters specsScope allocation n queue
      · exact queue
  | _ => exact queue

/-- Queue source-origin values are carried together with the already checked allocation
invariant during the actual expression walk. -/
theorem replaceAll_queueOriginValues (cx : XCtx) (np : Nat) (owner : Name)
    (lookup : cx.ind? = IndView.ofConst? cx.source.get?)
    (parameters : ∀ b ∈ cx.paramBinders, BinderScope (RunReach cx) b)
    (e : Expr) (depth : Nat) (st : XSt) (scope : ExpansionScope cx st)
    (seen : SeenRange st) (expression : RefScope (RunKnown cx st) e)
    (allocation : AllocationInvariant cx st) (n : Nat) (queue : QueueOriginValues cx n st) :
    QueueOriginValues cx n (replaceAll cx np owner e depth st).2 := by
  have preserve : ∀ (current : Expr) (d : Nat) (state : XSt),
      ExpansionScope cx state → SeenRange state → RefScope (RunKnown cx state) current →
      AllocationInvariant cx state ∧ QueueOriginValues cx n state →
      AllocationInvariant cx (replaceIfNested cx np owner current d state).2 ∧
        QueueOriginValues cx n (replaceIfNested cx np owner current d state).2 := by
    intro current d state scopedState _ refs invariant
    exact ⟨replaceIfNested_allocation cx np owner current d state lookup scopedState parameters refs invariant.1,
      replaceIfNested_queueOriginValues cx np owner current d state lookup scopedState parameters refs invariant.1 n invariant.2⟩
  exact (replaceAll_internalInvariant cx np owner lookup parameters
    (fun state => AllocationInvariant cx state ∧ QueueOriginValues cx n state) preserve
    e depth st scope seen expression ⟨allocation,queue⟩).2

/-- Actual names, including the source spelling retained by the runtime.
Constructor-type rewrites leave this whole observation unchanged. -/
def originMemberShape (member : XMember) : Name × List Name :=
  (member.name,member.ctors.toList.map fun ctor => ctor.name)

def originShapes (st : XSt) : List (Name × List Name) :=
  st.types.toList.map originMemberShape

/-- Exact name shape is sufficient to transport the source-origin witness. -/
theorem MemberOrigin.of_shape {cx : XCtx} {st : XSt} {before after : XMember}
    (origin : MemberOrigin cx st before)
    (same : originMemberShape after = originMemberShape before) : MemberOrigin cx st after := by
  have names : after.name = before.name := congrArg Prod.fst same
  apply origin.fields names
  intro generated present
  have constructors : after.ctors.toList.map (fun ctor => ctor.name) =
      before.ctors.toList.map (fun ctor => ctor.name) := congrArg Prod.snd same
  have mapped : generated.name ∈ after.ctors.toList.map (fun ctor => ctor.name) :=
    List.mem_map.mpr ⟨generated,by simpa using present,rfl⟩
  rw [constructors] at mapped
  obtain ⟨previous,inBefore,sameName⟩ := List.mem_map.mp mapped
  exact ⟨previous,by simpa using inBefore,sameName⟩

/-- Queue position and complete actual name shape retain all origin witnesses
when the origin tables extend. This covers the real constructor-type update. -/
theorem QueueOriginValues.shape {cx : XCtx} {n : Nat} {before after : XSt}
    (queue : QueueOriginValues cx n before) (same : originShapes after = originShapes before)
    (extension : OriginTablesExtend before after) : QueueOriginValues cx n after := by
  constructor
  · have sizes : after.types.size = before.types.size := by
      simpa [originShapes] using congrArg List.length same
    simpa only [sizes] using queue.originalBound
  · intro member present
    have mapped : originMemberShape member ∈ (originShapes after).drop n := by
      change originMemberShape member ∈ (after.types.toList.map originMemberShape).drop n
      rw [← List.map_drop]
      exact List.mem_map.mpr ⟨member,present,rfl⟩
    rw [same] at mapped
    change originMemberShape member ∈ (before.types.toList.map originMemberShape).drop n at mapped
    rw [← List.map_drop] at mapped
    obtain ⟨previous,inBefore,sameShape⟩ := List.mem_map.mp mapped
    exact ((queue.members previous inBefore).extend extension).of_shape sameShape.symm

/-- The selected constructor update changes only its type. Actual member and constructor names
retain their exact order while nested discovery may append new members. -/
theorem walkCtor_queueOriginValues (cx : XCtx) (qi ci : Nat) (st : XSt)
    (lookup : cx.ind? = IndView.ofConst? cx.source.get?)
    (parameters : ∀ b ∈ cx.paramBinders, BinderScope (RunReach cx) b)
    (scope : ExpansionScope cx st) (seen : SeenRange st)
    (allocation : AllocationInvariant cx st) (n : Nat) (queue : QueueOriginValues cx n st) :
    QueueOriginValues cx n (walkCtor cx qi ci st) := by
  unfold walkCtor
  split
  · exact queue
  · rename_i member foundMember
    split
    · exact queue
    · rename_i ctor foundCtor
      have constructorScope := (scope.members member (Array.mem_of_getElem? foundMember)).2
        ctor (Array.mem_of_getElem? foundCtor)
      have peeled := constructorScope.peelForalls cx.nParams #[] (by simp)
      generalize telescope : peelForalls cx.nParams ctor.typ #[] = pair at peeled ⊢
      obtain ⟨binders,body⟩ := pair
      dsimp only at peeled ⊢
      have queued := replaceAll_queueOriginValues cx binders.size member.sourceOwner
        lookup parameters body 0 st scope seen peeled.1 allocation n queue
      revert queued
      cases replaceAll cx binders.size member.sourceOwner body 0 st with
      | mk body' next =>
        intro queued
        let updated : XSt := { next with types := next.types.modify qi fun m =>
          { m with ctors := m.ctors.modify ci fun c =>
            { c with typ := mkForalls binders body' } } }
        change QueueOriginValues cx n updated
        apply QueueOriginValues.shape (after := updated) queued ?_ (OriginTablesExtend.fields rfl rfl)
        change (next.types.modify qi _).toList.map originMemberShape = next.types.toList.map originMemberShape
        apply array_modify_shape
        intro current
        apply Prod.ext
        · rfl
        · change (current.ctors.modify ci _).toList.map (fun c => c.name) =
            current.ctors.toList.map (fun c => c.name)
          apply array_modify_shape
          intro c
          rfl

/-- Every actual queue iteration preserves the complete source-origin
witnesses of the queued auxiliary suffix. The pending-error
and fuel branches are the existing executable branches. -/
theorem walkQueue_queueOriginValues (cx : XCtx)
    (lookup : cx.ind? = IndView.ofConst? cx.source.get?)
    (parameters : ∀ b ∈ cx.paramBinders, BinderScope (RunReach cx) b) (n : Nat) :
    ∀ (fuel qi : Nat) (st final : XSt), ExpansionScope cx st → SeenRange st →
      AllocationInvariant cx st → QueueOriginValues cx n st → walkQueue cx fuel qi st = .ok final →
      QueueOriginValues cx n final
  | 0,qi,st,final,scope,seen,allocation,queue,run => by
    rw [walkQueue.eq_1] at run
    split at run
    · cases run
    · split at run
      · cases run
      · cases except_pure_ok run
        exact queue
  | fuel+1,qi,st,final,scope,seen,allocation,queue,run => by
    rw [walkQueue.eq_2] at run
    split at run
    · cases run
    · split at run
      · cases except_pure_ok run
        exact queue
      · rename_i member found
        have step :
            let next := (List.range member.ctors.size).foldl (fun s ci => walkCtor cx qi ci s) st
            ExpansionScope cx next ∧ SeenRange next ∧ AllocationInvariant cx next ∧ QueueOriginValues cx n next := by
          dsimp only
          refine list_foldl_inv (fun s =>
            ExpansionScope cx s ∧ SeenRange s ∧ AllocationInvariant cx s ∧ QueueOriginValues cx n s)
            _ ?_ _ _ ⟨scope,seen,allocation,queue⟩
          intro current index invariant
          exact ⟨walkCtor_scope cx qi index current lookup parameters invariant.1 invariant.2.1,
            walkCtor_seenRange cx qi index current invariant.2.1,
            walkCtor_allocation cx qi index current lookup parameters invariant.1 invariant.2.1 invariant.2.2.1,
            walkCtor_queueOriginValues cx qi index current lookup parameters invariant.1 invariant.2.1 invariant.2.2.1 n invariant.2.2.2⟩
        exact walkQueue_queueOriginValues cx lookup parameters n fuel (qi+1) _ final
          step.1 step.2.1 step.2.2.1 step.2.2.2 run

/-- Every auxiliary in a successful real expansion has its actual source
inductive lookup, exact stored occurrence and source-constructor/owner values.
All scope, reference, allocation and initial-prefix facts come from the real
initializer and run; there is no new public source or freshness premise. -/
theorem expand_queueOriginValues (source : Ix.Environment) (dedup : Dedup)
    (classes : Array (Array Name)) (groupOf : SourceGroups)
    (keyAddr? : Option (Name → Option Address)) {x : Expanded}
    (run : expandSourceSpec source dedup (repsOf classes) (aliasesOf classes) groupOf keyAddr? = .ok x) :
    x.nOriginals ≤ x.types.size ∧
    ∀ member ∈ x.types.toList.drop x.nOriginals,
      ∃ (sourceName : Name) (view : IndView) (levels : Array Ix.Level) (specs : Array Expr),
        IndView.ofConst? source.get? sourceName = some view ∧
        x.auxToNested.get? member.name = some (mkAppN (Expr.mkConst sourceName levels) specs) ∧
        ∀ generated ∈ member.ctors, ∃ original ∈ view.ctors,
          x.auxCtorMap.get? generated.name = some (original.1,member.name) := by
  obtain ⟨first,fi,firstFound,viewFound,initial,final,initialRun,scope,parameters,queueRun,output⟩ :=
    expand_initialization source dedup classes groupOf keyAddr? run
  have seen : SeenRange initial := by
    intro key value member
    rw [initialMembers_seen (repsOf classes) (aliasesOf classes) initialRun] at member
    cases member
  have initialAllocation := initialMembers_allocation (repsOf classes) (aliasesOf classes) initialRun
  have finalValues := walkQueue_queueOriginValues _ rfl parameters initial.types.size expansionBound 0
    initial final scope seen ⟨[],initialAllocation⟩ (QueueOriginValues.initial _ initial) queueRun
  cases output
  exact ⟨finalValues.originalBound,finalValues.members⟩

end Ix.CompileCert.Canon
