import Ix.CompileCert.Canon.ExpansionAllocation

namespace Ix.CompileCert.Canon
open Ix.Compile.Canon
open Ix (Name Expr)

/-- Constructor identities in their actual queue order. -/
def queuedCtorKeys (ctors : Array XCtor) : List Lean.Name :=
  ctors.toList.map fun ctor => keyName ctor.name

/-- Member/constructor identity shape, independent of type rewrites. -/
def queuedMemberShape (member : XMember) : Lean.Name × List Lean.Name :=
  (keyName member.name,queuedCtorKeys member.ctors)

def queuedShapes (st : XSt) : List (Lean.Name × List Lean.Name) :=
  st.types.toList.map queuedMemberShape

theorem queuedCtorKeys_push (ctors : Array XCtor) (ctor : XCtor) :
    queuedCtorKeys (ctors.push ctor) = queuedCtorKeys ctors ++ [keyName ctor.name] := by
  simp [queuedCtorKeys,Array.toList_push]

theorem queuedShapes_push (st : XSt) (member : XMember) :
    queuedShapes (st.push member) = queuedShapes st ++ [queuedMemberShape member] := by
  simp [queuedShapes,XSt.push,Array.toList_push]

/-- Changing array entries while preserving their observed shape preserves
its complete ordered list, including multiplicity. -/
theorem array_modify_shape {α β : Type} (xs : Array α) (index : Nat)
    (update : α → α) (shape : α → β) (same : ∀ x, shape (update x) = shape x) :
    (xs.modify index update).toList.map shape = xs.toList.map shape := by
  apply List.ext_getElem?
  intro i
  rw [List.getElem?_map,List.getElem?_map,Array.getElem?_toList,
    Array.getElem?_toList,Array.getElem?_modify]
  split
  · cases xs[i]? with
    | none => rfl
    | some x => simp only [Option.map_some,same x]
  · rfl

/-- The real constructor loop prepends its new constructor roots in reverse
constructor order and leaves the auxiliary-origin table untouched. -/
theorem nestedCtors_originHistory (cx : XCtx) (sourceName auxName : Name)
    (view : IndView) (externalParams : Nat) (levels : Array Ix.Level)
    (specs : Array Expr) (sourceNames : List Lean.Name) (st : XSt) :
    let result := nestedCtors cx sourceName auxName view externalParams levels specs sourceNames st
    result.1.auxToNested.entries = st.auxToNested.entries ∧
      result.1.allocatedCtorRoots = (queuedCtorKeys result.2).reverse ++ st.allocatedCtorRoots := by
  unfold nestedCtors
  refine forIn_id_inv_array (fun q : XSt × Array XCtor =>
    q.1.auxToNested.entries = st.auxToNested.entries ∧
      q.1.allocatedCtorRoots = (queuedCtorKeys q.2).reverse ++ st.allocatedCtorRoots)
    _ ?_ _ _ ?_
  · intro sourceCtor q previous
    obtain ⟨cn,ct,nf⟩ := sourceCtor
    constructor
    · exact previous.1
    · change keyName _ :: q.1.allocatedCtorRoots =
        (queuedCtorKeys (q.2.push _)).reverse ++ st.allocatedCtorRoots
      simp [queuedCtorKeys_push,previous.2,List.reverse_append]
  · simp [queuedCtorKeys]

/-- The fixed original prefix may be dropped before or after an append. -/
theorem drop_append_prefix {α : Type} (xs ys : List α) (n : Nat)
    (bound : n ≤ xs.length) : (xs ++ ys).drop n = xs.drop n ++ ys := by
  induction xs generalizing n with
  | nil =>
    have : n = 0 := Nat.eq_zero_of_le_zero bound
    subst n
    rfl
  | cons x xs ih =>
    cases n with
    | zero => rfl
    | succ n =>
      simpa using ih n (Nat.le_of_succ_le_succ bound)

/-- Stable query/queue states tie both origin-table key lists to the actual
auxiliary members and constructors after the fixed original prefix. -/
structure QueueOrigins (nOriginals : Nat) (st : XSt) : Prop where
  originalBound : nOriginals ≤ st.types.size
  auxiliaries : st.auxToNested.entries.map (fun entry => keyName entry.1) =
    ((queuedShapes st).drop nOriginals |>.map Prod.fst).reverse
  constructors : st.auxCtorMap.entries.map (fun entry => keyName entry.1) =
    ((queuedShapes st).drop nOriginals |>.flatMap Prod.snd).reverse

/-- At initialization there is no auxiliary allocation, so dropping the
actual original prefix leaves exactly the two empty origin-key lists. -/
theorem QueueOrigins.initial {cx : XCtx} {st : XSt}
    (allocation : AllocationState cx [] st) : QueueOrigins st.types.size st := by
  have noCtors : st.allocatedCtorRoots = [] := by
    cases h : st.allocatedCtorRoots with
    | nil => rfl
    | cons ctor rest =>
      have member : ctor ∈ st.allocatedCtorRoots := by simp [h]
      obtain ⟨owner,owned,_,_⟩ := allocation.forest.ctorOwner ctor member
      cases owned
  have empty : (queuedShapes st).drop st.types.size = [] := by
    simp [queuedShapes]
  constructor
  · exact Nat.le_refl _
  · simpa [empty] using allocation.rootKeys
  · simpa [empty,noCtors] using allocation.ctorKeys

/-- Pushing the just-built member turns the two actual insertion histories
into the reverse of the complete auxiliary queue, without reordering it. -/
theorem QueueOrigins.push {n : Nat} {before after : XSt}
    (queue : QueueOrigins n before) (member : XMember)
    (types : after.types = before.types)
    (auxiliaries : after.auxToNested.entries.map (fun entry => keyName entry.1) =
      keyName member.name :: before.auxToNested.entries.map (fun entry => keyName entry.1))
    (constructors : after.auxCtorMap.entries.map (fun entry => keyName entry.1) =
      (queuedCtorKeys member.ctors).reverse ++
        before.auxCtorMap.entries.map (fun entry => keyName entry.1)) :
    QueueOrigins n (after.push member) := by
  have shapes : queuedShapes after = queuedShapes before := by
    simp only [queuedShapes,types]
  have bound : n ≤ (queuedShapes before).length := by
    simpa [queuedShapes] using queue.originalBound
  constructor
  · simpa only [XSt.push,Array.size_push,types] using
      Nat.le_trans queue.originalBound (Nat.le_succ before.types.size)
  · change after.auxToNested.entries.map (fun entry => keyName entry.1) = _
    rw [queuedShapes_push,shapes,drop_append_prefix _ _ _ bound]
    simp only [List.map_append,List.map_cons,List.map_nil,List.reverse_append,
      List.reverse_cons,List.reverse_nil,List.nil_append,List.singleton_append,queuedMemberShape]
    rw [← queue.auxiliaries]
    exact auxiliaries
  · change after.auxCtorMap.entries.map (fun entry => keyName entry.1) = _
    rw [queuedShapes_push,shapes,drop_append_prefix _ _ _ bound]
    simp only [List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,
      List.reverse_append,queuedMemberShape]
    rw [← queue.constructors]
    exact constructors

/-- One actual class step appends exactly the auxiliary whose origin was
inserted, with exactly its constructor history. This is an internal state
invariant; the public expansion theorem supplies every scope premise. -/
theorem nestedClassStep_queueOrigins (cx : XCtx) (owner : Name) (externalParams : Nat)
    (levels : Array Ix.Level) (specs : Array Expr) (original : Expr)
    (keyOf : Expr → Except String OccurrenceInput) (head : Name)
    (repl : Name → Expr) (cls : Array Name) (state next : XSt × Option Expr)
    (lookup : cx.ind? = IndView.ofConst? cx.source.get?)
    (scope : ExpansionScope cx state.1) (roots : List Lean.Name)
    (allocation : AllocationState cx roots state.1)
    (reached : ∀ name ∈ cls, RunReach cx name)
    (n : Nat) (queue : QueueOrigins n state.1)
    (run : nestedClassStep cx owner externalParams levels specs original keyOf head repl cls state =
      .yield next) : QueueOrigins n next.1 := by
  have finalAllocation := nestedClassStep_allocation cx owner externalParams levels specs original
    keyOf head repl cls state next lookup scope roots allocation reached run
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
      rw [sameState] at finalAllocation ⊢
      obtain ⟨nextRoots,finalAllocation⟩ := finalAllocation
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
      have ctorFields := nestedCtors_fields cx name auxName view externalParams levels specs sourceNames registered
      have history := nestedCtors_originHistory cx name auxName view externalParams levels specs sourceNames registered
      apply queue.push member
      · exact ctorFields.1.trans cacheFields.1
      · change result.1.auxToNested.entries.map (fun entry => keyName entry.1) = _
        rw [history.1,cacheAllocation.2.2.1]
        simpa only [allocation.rootKeys] using preparedAllocation.rootKeys
      · have actual := finalAllocation.ctorKeys
        change result.1.auxCtorMap.entries.map (fun entry => keyName entry.1) =
          result.1.allocatedCtorRoots at actual
        rw [actual,history.2,cacheAllocation.2.1]
        change (queuedCtorKeys result.2).reverse ++ state.1.allocatedCtorRoots = _
        rw [allocation.ctorKeys]
    · cases run
      exact queue
  · cases run
    exact queue


/-- Queue identity shape and the exact ordered origin-table entries are the
only state fields read by this invariant. -/
theorem QueueOrigins.fields {n : Nat} {st next : XSt} (queue : QueueOrigins n st)
    (shapes : queuedShapes next = queuedShapes st)
    (auxiliaries : next.auxToNested.entries = st.auxToNested.entries)
    (constructors : next.auxCtorMap.entries = st.auxCtorMap.entries) :
    QueueOrigins n next := by
  have sameSize : next.types.size = st.types.size := by
    simpa [queuedShapes] using congrArg List.length shapes
  constructor
  · simpa only [sameSize] using queue.originalBound
  · simpa only [auxiliaries,shapes] using queue.auxiliaries
  · simpa only [constructors,shapes] using queue.constructors

/-- The actual class loop carries the fixed original prefix and both ordered
origin histories through every class, including skipped classes. Its scope
and allocation facts are internal invariants from the real query. -/
theorem nestedClasses_queueOrigins (cx : XCtx) (np : Nat) (owner : Name)
    (levels : Array Ix.Level) (specs : Array Expr) (original : Expr)
    (keyOf : Expr → Except String OccurrenceInput) (head : Name)
    (repl : Name → Expr) (view : IndView) (st : XSt)
    (lookup : cx.ind? = IndView.ofConst? cx.source.get?)
    (query : RunReach cx head) (found : cx.ind? head = some view)
    (scope : ExpansionScope cx st)
    (parameters : ∀ b ∈ cx.paramBinders, BinderScope (RunReach cx) b)
    (arguments : ∀ e ∈ specs, RefScope (RunKnown cx st) e)
    (allocation : AllocationInvariant cx st) (n : Nat) (queue : QueueOrigins n st) :
    QueueOrigins n
      (forIn (m := Id) (cx.groupOf view) (st,none)
        (nestedClassStep cx owner np levels specs original keyOf head repl)).1 := by
  have all :
      let result := forIn (m := Id) (cx.groupOf view) (st,none)
        (nestedClassStep cx owner np levels specs original keyOf head repl)
      ExpansionScope cx result.1 ∧ ExpansionFrame cx st result.1 ∧
        AllocationInvariant cx result.1 ∧ QueueOrigins n result.1 := by
    dsimp only
    refine forIn_id_inv_array_mem (fun state : XSt × Option Expr =>
      ExpansionScope cx state.1 ∧ ExpansionFrame cx st state.1 ∧
        AllocationInvariant cx state.1 ∧ QueueOrigins n state.1)
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
      nestedClassStep_queueOrigins cx owner np levels specs original keyOf head repl cls state next
        lookup invariant.1 roots allocated reached n invariant.2.2.2 step⟩
    intro e inSpecs
    exact (arguments e inSpecs).mono (fun _ known => known.frame invariant.2.1)
  exact all.2.2.2

private theorem queueOrigins_id_pure {α : Type} (value : α) : (pure value : Id α) = value := rfl

/-- Every actual query branch preserves queue/origin alignment. The error
branch changes only the pending error; hits and ineligible expressions retain
state, and the miss branch is the actual complete class loop. -/
theorem replaceIfNested_queueOrigins (cx : XCtx) (np : Nat) (owner : Name)
    (e : Expr) (depth : Nat) (st : XSt)
    (lookup : cx.ind? = IndView.ofConst? cx.source.get?)
    (scope : ExpansionScope cx st)
    (parameters : ∀ b ∈ cx.paramBinders, BinderScope (RunReach cx) b)
    (expression : RefScope (RunKnown cx st) e)
    (allocation : AllocationInvariant cx st) (n : Nat) (queue : QueueOrigins n st) :
    QueueOrigins n (replaceIfNested cx np owner e depth st).2 := by
  rw [replaceIfNested_group_def]
  simp only [id_bind_eq,queueOrigins_id_pure]
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
              · exact queue.fields rfl rfl rfl
              · split
                · exact queue
                · dsimp only
                  exact nestedClasses_queueOrigins cx view.numParams owner levels
                    ((args.extract 0 view.numParams).map (lowerLoose · depth))
                    (mkAppN (Expr.mkConst name levels) ((args.extract 0 view.numParams).map (lowerLoose · depth)))
                    _ name _ view st lookup query foundView scope parameters specsScope allocation n queue
      · exact queue
  | _ => exact queue

/-- A state predicate preserved by actual queries is preserved by the actual
preorder traversal. Scope/cache premises are precisely the existing internal
run invariants; no runtime implementation or endpoint domain changes. -/
theorem replaceAll_internalInvariant (cx : XCtx) (np : Nat) (owner : Name)
    (lookup : cx.ind? = IndView.ofConst? cx.source.get?)
    (parameters : ∀ b ∈ cx.paramBinders, BinderScope (RunReach cx) b)
    (P : XSt → Prop)
    (queryPreserves : ∀ (e : Expr) (depth : Nat) (st : XSt),
      ExpansionScope cx st → SeenRange st → RefScope (RunKnown cx st) e →
      P st → P (replaceIfNested cx np owner e depth st).2) :
    ∀ (e : Expr) (depth : Nat) (st : XSt), ExpansionScope cx st → SeenRange st →
      RefScope (RunKnown cx st) e → P st →
      P (replaceAll cx np owner e depth st).2 := by
  intro e
  induction e with
  | app f a hash ihf iha =>
    intro d st scope seen expression invariant
    rw [replaceAll.eq_1]
    have allocated := queryPreserves (.app f a hash) d st scope seen expression invariant
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
    intro d st scope seen expression invariant
    rw [replaceAll.eq_1]
    have allocated := queryPreserves (.lam name typ body info hash) d st scope seen expression invariant
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
    intro d st scope seen expression invariant
    rw [replaceAll.eq_1]
    have allocated := queryPreserves (.forallE name typ body info hash) d st scope seen expression invariant
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
    intro d st scope seen expression invariant
    rw [replaceAll.eq_1]
    have allocated := queryPreserves (.letE name typ value body nonDep hash) d st scope seen expression invariant
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
    intro d st scope seen expression invariant
    rw [replaceAll.eq_1]
    have allocated := queryPreserves (.proj name index body hash) d st scope seen expression invariant
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
    intro d st scope seen expression invariant
    rw [replaceAll.eq_1]
    have allocated := queryPreserves (.mdata data body hash) d st scope seen expression invariant
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
    intro d st scope seen expression invariant
    rw [replaceAll.eq_1]
    have next := queryPreserves (.bvar index hash) d st scope seen expression invariant
    revert next
    cases replaceIfNested cx np owner (.bvar index hash) d st with
    | mk result st1 => intro next; cases result <;> exact next
  | fvar name hash =>
    intro d st scope seen expression invariant
    rw [replaceAll.eq_1]
    have next := queryPreserves (.fvar name hash) d st scope seen expression invariant
    revert next
    cases replaceIfNested cx np owner (.fvar name hash) d st with
    | mk result st1 => intro next; cases result <;> exact next
  | mvar name hash =>
    intro d st scope seen expression invariant
    rw [replaceAll.eq_1]
    have next := queryPreserves (.mvar name hash) d st scope seen expression invariant
    revert next
    cases replaceIfNested cx np owner (.mvar name hash) d st with
    | mk result st1 => intro next; cases result <;> exact next
  | sort level hash =>
    intro d st scope seen expression invariant
    rw [replaceAll.eq_1]
    have next := queryPreserves (.sort level hash) d st scope seen expression invariant
    revert next
    cases replaceIfNested cx np owner (.sort level hash) d st with
    | mk result st1 => intro next; cases result <;> exact next
  | const name levels hash =>
    intro d st scope seen expression invariant
    rw [replaceAll.eq_1]
    have next := queryPreserves (.const name levels hash) d st scope seen expression invariant
    revert next
    cases replaceIfNested cx np owner (.const name levels hash) d st with
    | mk result st1 => intro next; cases result <;> exact next
  | lit literal hash =>
    intro d st scope seen expression invariant
    rw [replaceAll.eq_1]
    have next := queryPreserves (.lit literal hash) d st scope seen expression invariant
    revert next
    cases replaceIfNested cx np owner (.lit literal hash) d st with
    | mk result st1 => intro next; cases result <;> exact next

/-- Queue alignment is carried together with the already checked allocation
invariant during the actual expression walk. -/
theorem replaceAll_queueOrigins (cx : XCtx) (np : Nat) (owner : Name)
    (lookup : cx.ind? = IndView.ofConst? cx.source.get?)
    (parameters : ∀ b ∈ cx.paramBinders, BinderScope (RunReach cx) b)
    (e : Expr) (depth : Nat) (st : XSt) (scope : ExpansionScope cx st)
    (seen : SeenRange st) (expression : RefScope (RunKnown cx st) e)
    (allocation : AllocationInvariant cx st) (n : Nat) (queue : QueueOrigins n st) :
    QueueOrigins n (replaceAll cx np owner e depth st).2 := by
  have preserve : ∀ (current : Expr) (d : Nat) (state : XSt),
      ExpansionScope cx state → SeenRange state → RefScope (RunKnown cx state) current →
      AllocationInvariant cx state ∧ QueueOrigins n state →
      AllocationInvariant cx (replaceIfNested cx np owner current d state).2 ∧
        QueueOrigins n (replaceIfNested cx np owner current d state).2 := by
    intro current d state scopedState _ refs invariant
    exact ⟨replaceIfNested_allocation cx np owner current d state lookup scopedState parameters refs invariant.1,
      replaceIfNested_queueOrigins cx np owner current d state lookup scopedState parameters refs invariant.1 n invariant.2⟩
  exact (replaceAll_internalInvariant cx np owner lookup parameters
    (fun state => AllocationInvariant cx state ∧ QueueOrigins n state) preserve
    e depth st scope seen expression ⟨allocation,queue⟩).2

/-- The selected constructor update changes only its type. Both queue lists
retain their exact order while nested discovery may append new members. -/
theorem walkCtor_queueOrigins (cx : XCtx) (qi ci : Nat) (st : XSt)
    (lookup : cx.ind? = IndView.ofConst? cx.source.get?)
    (parameters : ∀ b ∈ cx.paramBinders, BinderScope (RunReach cx) b)
    (scope : ExpansionScope cx st) (seen : SeenRange st)
    (allocation : AllocationInvariant cx st) (n : Nat) (queue : QueueOrigins n st) :
    QueueOrigins n (walkCtor cx qi ci st) := by
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
      have queued := replaceAll_queueOrigins cx binders.size member.sourceOwner
        lookup parameters body 0 st scope seen peeled.1 allocation n queue
      revert queued
      cases replaceAll cx binders.size member.sourceOwner body 0 st with
      | mk body' next =>
        intro queued
        let updated : XSt := { next with types := next.types.modify qi fun m =>
          { m with ctors := m.ctors.modify ci fun c =>
            { c with typ := mkForalls binders body' } } }
        change QueueOrigins n updated
        apply QueueOrigins.fields (next := updated) queued ?_ rfl rfl
        change (next.types.modify qi _).toList.map queuedMemberShape = next.types.toList.map queuedMemberShape
        apply array_modify_shape
        intro current
        apply Prod.ext
        · rfl
        · change (current.ctors.modify ci _).toList.map (fun c => keyName c.name) =
            current.ctors.toList.map (fun c => keyName c.name)
          apply array_modify_shape
          intro c
          rfl

/-- Every actual queue iteration preserves both origin tables' ordered
correspondence to the queued auxiliary/constructor suffix. The pending-error
and fuel branches are the existing executable branches. -/
theorem walkQueue_queueOrigins (cx : XCtx)
    (lookup : cx.ind? = IndView.ofConst? cx.source.get?)
    (parameters : ∀ b ∈ cx.paramBinders, BinderScope (RunReach cx) b) (n : Nat) :
    ∀ (fuel qi : Nat) (st final : XSt), ExpansionScope cx st → SeenRange st →
      AllocationInvariant cx st → QueueOrigins n st → walkQueue cx fuel qi st = .ok final →
      QueueOrigins n final
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
            ExpansionScope cx next ∧ SeenRange next ∧ AllocationInvariant cx next ∧ QueueOrigins n next := by
          dsimp only
          refine list_foldl_inv (fun s =>
            ExpansionScope cx s ∧ SeenRange s ∧ AllocationInvariant cx s ∧ QueueOrigins n s)
            _ ?_ _ _ ⟨scope,seen,allocation,queue⟩
          intro current index invariant
          exact ⟨walkCtor_scope cx qi index current lookup parameters invariant.1 invariant.2.1,
            walkCtor_seenRange cx qi index current invariant.2.1,
            walkCtor_allocation cx qi index current lookup parameters invariant.1 invariant.2.1 invariant.2.2.1,
            walkCtor_queueOrigins cx qi index current lookup parameters invariant.1 invariant.2.1 invariant.2.2.1 n invariant.2.2.2⟩
        exact walkQueue_queueOrigins cx lookup parameters n fuel (qi+1) _ final
          step.1 step.2.1 step.2.2.1 step.2.2.2 run

/-- Successful expansion's exact ordered origin keys are the reverse of the
actual auxiliary and constructor queues after the original prefix. Every
scope, reachability, allocation and initial-history premise is discharged by
the real initializer; no new public source/domain premise is introduced. -/
theorem expand_queueOrigins (source : Ix.Environment) (dedup : Dedup)
    (classes : Array (Array Name)) (groupOf : SourceGroups)
    (keyAddr? : Option (Name → Option Address)) {x : Expanded}
    (run : expandSourceSpec source dedup (repsOf classes) (aliasesOf classes) groupOf keyAddr? = .ok x) :
    x.nOriginals ≤ x.types.size ∧
      x.auxToNested.entries.map (fun entry => keyName entry.1) =
        ((x.types.toList.map queuedMemberShape).drop x.nOriginals |>.map Prod.fst).reverse ∧
      x.auxCtorMap.entries.map (fun entry => keyName entry.1) =
        ((x.types.toList.map queuedMemberShape).drop x.nOriginals |>.flatMap Prod.snd).reverse := by
  obtain ⟨first,fi,firstFound,viewFound,initial,final,initialRun,scope,parameters,queueRun,output⟩ :=
    expand_initialization source dedup classes groupOf keyAddr? run
  have seen : SeenRange initial := by
    intro key value member
    rw [initialMembers_seen (repsOf classes) (aliasesOf classes) initialRun] at member
    cases member
  have initialAllocation := initialMembers_allocation (repsOf classes) (aliasesOf classes) initialRun
  have finalQueue := walkQueue_queueOrigins _ rfl parameters initial.types.size expansionBound 0
    initial final scope seen ⟨[],initialAllocation⟩ (QueueOrigins.initial initialAllocation) queueRun
  cases output
  exact ⟨finalQueue.originalBound,finalQueue.auxiliaries,finalQueue.constructors⟩

end Ix.CompileCert.Canon
