import Ix.CompileCert.Canon.ExpansionScopeStep

namespace Ix.CompileCert.Canon
open Ix.Compile.Canon
open Ix (Name Expr)

/-- A class result is absent or replaces the query with an actual queued
auxiliary; no injectivity assumption on the replacement function is needed. -/
def NestedResultRange (repl : Name → Expr) (state : XSt × Option Expr) : Prop :=
  state.2 = none ∨ ∃ aux, state.1.typeNames.contains aux = true ∧ state.2 = some (repl aux)

theorem nestedClassStep_yield (cx : XCtx) (owner : Name) (externalParams : Nat)
    (levels : Array Ix.Level) (specs : Array Expr) (original : Expr)
    (keyOf : Expr → Except String OccurrenceInput) (head : Name)
    (repl : Name → Expr) (cls : Array Name) (state : XSt × Option Expr) :
    ∃ next, nestedClassStep cx owner externalParams levels specs original keyOf head repl cls state =
      .yield next := by
  unfold nestedClassStep
  repeat' first | exact ⟨_,rfl⟩ | split

theorem nestedClassStep_resultRange (cx : XCtx) (owner : Name) (externalParams : Nat)
    (levels : Array Ix.Level) (specs : Array Expr) (original : Expr)
    (keyOf : Expr → Except String OccurrenceInput) (head : Name)
    (repl : Name → Expr) (cls : Array Name) (state next : XSt × Option Expr)
    (range : NestedResultRange repl state)
    (run : nestedClassStep cx owner externalParams levels specs original keyOf head repl cls state =
      .yield next) : NestedResultRange repl next := by
  have frame := nestedClassStep_frame cx owner externalParams levels specs original keyOf head repl cls state next run
  unfold nestedClassStep at run
  repeat' split at run
  all_goals
    cases run
    first
    | exact range
    | exact Or.inr ⟨_,NameTable.contains_insert_self _ _ (),rfl⟩
    | (rcases range with empty | ⟨aux,queued,equal⟩
       · exact Or.inl empty
       · exact Or.inr ⟨aux,frame.1 aux queued,equal⟩)

/-- The real external-group loop preserves source/member scope and the
replacement's queued identity, for every actually registered class it visits. -/
theorem nestedClasses_scope (cx : XCtx) (np : Nat) (owner : Name)
    (levels : Array Ix.Level) (specs : Array Expr) (original : Expr)
    (keyOf : Expr → Except String OccurrenceInput) (head : Name)
    (repl : Name → Expr) (view : IndView) (st : XSt)
    (lookup : cx.ind? = IndView.ofConst? cx.source.get?)
    (query : RunReach cx head) (found : cx.ind? head = some view)
    (scope : ExpansionScope cx st)
    (parameters : ∀ b ∈ cx.paramBinders, BinderScope (RunReach cx) b)
    (arguments : ∀ e ∈ specs, RefScope (RunKnown cx st) e) :
    let result := forIn (m := Id) (cx.groupOf view) (st,none)
      (nestedClassStep cx owner np levels specs original keyOf head repl)
    ExpansionScope cx result.1 ∧ ExpansionFrame cx st result.1 ∧ NestedResultRange repl result := by
  dsimp only
  refine forIn_id_inv_array_mem (fun state : XSt × Option Expr =>
    ExpansionScope cx state.1 ∧ ExpansionFrame cx st state.1 ∧ NestedResultRange repl state)
    _ _ _ ⟨scope,ExpansionFrame.refl cx st,Or.inl rfl⟩ ?_
  intro cls member state invariant
  obtain ⟨next,step⟩ := nestedClassStep_yield cx owner np levels specs original keyOf head repl cls state
  rw [step]
  have stepFrame := nestedClassStep_frame cx owner np levels specs original keyOf head repl cls state next step
  refine ⟨nestedClassStep_expansionScope cx owner np levels specs original keyOf head repl cls state next
    lookup invariant.1 parameters ?_ ?_ step,
    invariant.2.1.trans stepFrame,
    nestedClassStep_resultRange cx owner np levels specs original keyOf head repl cls state next invariant.2.2 step⟩
  · intro e inSpecs
    exact (arguments e inSpecs).mono (fun _ known => known.frame invariant.2.1)
  · intro name inClass
    apply query.groupMember (groups := cx.groupOf) ?_ member inClass
    simpa [lookup] using found



/-- The class loop's result theorem abstracts over its actual key callback;
reference scope never needs to identify or duplicate that callback. -/
theorem nestedClasses_resultScope (cx : XCtx) (np : Nat) (owner : Name)
    (levels : Array Ix.Level) (specs : Array Expr) (original : Expr)
    (keyOf : Expr → Except String OccurrenceInput) (head : Name)
    (repl : Name → Expr) (view : IndView) (st : XSt)
    (lookup : cx.ind? = IndView.ofConst? cx.source.get?)
    (query : RunReach cx head) (found : cx.ind? head = some view)
    (scope : ExpansionScope cx st)
    (parameters : ∀ b ∈ cx.paramBinders, BinderScope (RunReach cx) b)
    (arguments : ∀ e ∈ specs, RefScope (RunKnown cx st) e)
    (replacement : ∀ next, ExpansionFrame cx st next → ∀ aux,
      next.typeNames.contains aux = true → RefScope (RunKnown cx next) (repl aux)) :
    let result := forIn (m := Id) (cx.groupOf view) (st,none)
      (nestedClassStep cx owner np levels specs original keyOf head repl)
    ExpansionScope cx result.1 ∧ ∀ value, result.2 = some value →
      RefScope (RunKnown cx result.1) value := by
  have batch := nestedClasses_scope cx np owner levels specs original keyOf head repl view st
    lookup query found scope parameters arguments
  refine ⟨batch.1,?_⟩
  intro value output
  rcases batch.2.2 with empty | ⟨aux,queued,equal⟩
  · cases empty.symm.trans output
  · have same : value = repl aux := Option.some.inj (output.symm.trans equal)
    subst value
    exact replacement _ batch.2.1 aux queued

private theorem query_id_pure {α : Type} (value : α) : (pure value : Id α) = value := rfl

/-- The actual query preserves the queued members' scope and every returned
replacement's reference scope. Source and parameter facts are supplied by the
actual initializer; the cache range comes from the independently checked run. -/
theorem replaceIfNested_scope (cx : XCtx) (np : Nat) (owner : Name)
    (e : Expr) (depth : Nat) (st : XSt)
    (lookup : cx.ind? = IndView.ofConst? cx.source.get?)
    (scope : ExpansionScope cx st) (seen : SeenRange st)
    (parameters : ∀ b ∈ cx.paramBinders, BinderScope (RunReach cx) b)
    (expression : RefScope (RunKnown cx st) e) :
    ExpansionScope cx (replaceIfNested cx np owner e depth st).2 ∧
    ∀ value, (replaceIfNested cx np owner e depth st).1 = some value →
      RefScope (RunKnown cx (replaceIfNested cx np owner e depth st).2) value := by
  rw [replaceIfNested_group_def]
  simp only [id_bind_eq,query_id_pure]
  generalize appView : getAppFnArgs e = pair
  obtain ⟨head,args⟩ := pair
  cases head with
  | const name levels hash =>
    dsimp only [Id.run]
    split
    · exact ⟨scope,by intro value found; cases found⟩
    · rename_i notQueued
      have outside : st.typeNames.contains name = false := Bool.eq_false_iff.mpr notQueued
      split
      · rename_i view foundView
        split
        · exact ⟨scope,by intro value found; cases found⟩
        · split
          · exact ⟨scope,by intro value found; cases found⟩
          · split
            · exact ⟨scope,by intro value found; cases found⟩
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
              · exact ⟨⟨scope.members,scope.sourceCache⟩,by intro value found; cases found⟩
              · rename_i key normalized
                split
                · rename_i aux cached
                  refine ⟨scope,?_⟩
                  intro value equal
                  cases equal
                  have replacement := expression.nestedReplacement aux (Or.inr (seen.get cached))
                    cx.blockLevels np depth view.numParams
                  simpa only [appView] using replacement
                · dsimp only
                  apply nestedClasses_resultScope cx view.numParams owner levels
                    ((args.extract 0 view.numParams).map (lowerLoose · depth))
                    (mkAppN (Expr.mkConst name levels) ((args.extract 0 view.numParams).map (lowerLoose · depth)))
                    _ name _ view st lookup query foundView scope parameters specsScope
                  intro next frame aux queued
                  apply RefScope.mkAppN
                  · apply RefScope.mkAppN
                    · simpa [RefScope] using (show RunKnown cx next aux from Or.inr queued)
                    · exact RefScope.paramArgs _ np depth
                  · intro argument inExtract
                    obtain ⟨index,bound,rfl⟩ := Array.mem_extract_iff_getElem.mp inExtract
                    exact (argsScope _ (Array.getElem_mem _)).mono
                      (fun _ known => known.frame frame)
      · exact ⟨scope,by intro value found; cases found⟩
  | _ => exact ⟨scope,by intro value found; cases found⟩


/-- Pre-order replacement preserves the actual queue scope and the rewritten
expression's reference scope. The source/parameter facts are fixed by the
initializer, and the cache invariant is preserved by the real transitions. -/
theorem replaceAll_scope (cx : XCtx) (np : Nat) (owner : Name)
    (lookup : cx.ind? = IndView.ofConst? cx.source.get?)
    (parameters : ∀ b ∈ cx.paramBinders, BinderScope (RunReach cx) b) :
    ∀ (e : Expr) (depth : Nat) (st : XSt), ExpansionScope cx st → SeenRange st →
      RefScope (RunKnown cx st) e →
      ExpansionScope cx (replaceAll cx np owner e depth st).2 ∧
      RefScope (RunKnown cx (replaceAll cx np owner e depth st).2)
        (replaceAll cx np owner e depth st).1 := by
  intro e
  induction e with
  | app f a hash ihf iha =>
    intro d st scope seen expression
    rw [replaceAll.eq_1]
    have query := replaceIfNested_scope cx np owner (.app f a hash) d st lookup scope seen parameters expression
    have frame := replaceIfNested_frame cx np owner (.app f a hash) d st
    have cached := replaceIfNested_seenRange cx np owner (.app f a hash) d st seen
    revert query frame cached
    cases replaceIfNested cx np owner (.app f a hash) d st with
    | mk result st1 =>
      intro query frame cached
      cases result with
      | some value => exact ⟨query.1,query.2 value rfl⟩
      | none =>
        dsimp only
        have parts : RefScope (RunKnown cx st) f ∧ RefScope (RunKnown cx st) a := by
          simpa [RefScope,sourceExprRefs,or_imp,forall_and] using expression
        have first := ihf d st1 query.1 cached
          (parts.1.mono (fun _ known => known.frame frame))
        have frame1 := replaceAll_frame cx np owner f d st1
        have seen1 := replaceAll_seenRange cx np owner f d st1 cached
        revert first frame1 seen1
        cases replaceAll cx np owner f d st1 with
        | mk left st2 =>
          intro first frame1 seen1
          have second := iha d st2 first.1 seen1
            (parts.2.mono (fun _ known => known.frame (frame.trans frame1)))
          have frame2 := replaceAll_frame cx np owner a d st2
          revert second frame2
          cases replaceAll cx np owner a d st2 with
          | mk right st3 =>
            intro second frame2
            refine ⟨second.1,?_⟩
            have leftScope := first.2.mono (fun _ known => known.frame frame2)
            simpa [RefScope,sourceExprRefs,or_imp,forall_and] using And.intro leftScope second.2
  | lam name typ body info hash iht ihb =>
    intro d st scope seen expression
    rw [replaceAll.eq_1]
    have query := replaceIfNested_scope cx np owner (.lam name typ body info hash) d st lookup scope seen parameters expression
    have frame := replaceIfNested_frame cx np owner (.lam name typ body info hash) d st
    have cached := replaceIfNested_seenRange cx np owner (.lam name typ body info hash) d st seen
    revert query frame cached
    cases replaceIfNested cx np owner (.lam name typ body info hash) d st with
    | mk result st1 =>
      intro query frame cached
      cases result with
      | some value => exact ⟨query.1,query.2 value rfl⟩
      | none =>
        dsimp only
        have parts : RefScope (RunKnown cx st) typ ∧ RefScope (RunKnown cx st) body := by
          simpa [RefScope,sourceExprRefs,or_imp,forall_and] using expression
        have first := iht d st1 query.1 cached
          (parts.1.mono (fun _ known => known.frame frame))
        have frame1 := replaceAll_frame cx np owner typ d st1
        have seen1 := replaceAll_seenRange cx np owner typ d st1 cached
        revert first frame1 seen1
        cases replaceAll cx np owner typ d st1 with
        | mk left st2 =>
          intro first frame1 seen1
          have second := ihb (d+1) st2 first.1 seen1
            (parts.2.mono (fun _ known => known.frame (frame.trans frame1)))
          have frame2 := replaceAll_frame cx np owner body (d+1) st2
          revert second frame2
          cases replaceAll cx np owner body (d+1) st2 with
          | mk right st3 =>
            intro second frame2
            refine ⟨second.1,?_⟩
            have leftScope := first.2.mono (fun _ known => known.frame frame2)
            simpa [RefScope,sourceExprRefs,or_imp,forall_and] using And.intro leftScope second.2
  | forallE name typ body info hash iht ihb =>
    intro d st scope seen expression
    rw [replaceAll.eq_1]
    have query := replaceIfNested_scope cx np owner (.forallE name typ body info hash) d st lookup scope seen parameters expression
    have frame := replaceIfNested_frame cx np owner (.forallE name typ body info hash) d st
    have cached := replaceIfNested_seenRange cx np owner (.forallE name typ body info hash) d st seen
    revert query frame cached
    cases replaceIfNested cx np owner (.forallE name typ body info hash) d st with
    | mk result st1 =>
      intro query frame cached
      cases result with
      | some value => exact ⟨query.1,query.2 value rfl⟩
      | none =>
        dsimp only
        have parts : RefScope (RunKnown cx st) typ ∧ RefScope (RunKnown cx st) body := by
          simpa [RefScope,sourceExprRefs,or_imp,forall_and] using expression
        have first := iht d st1 query.1 cached
          (parts.1.mono (fun _ known => known.frame frame))
        have frame1 := replaceAll_frame cx np owner typ d st1
        have seen1 := replaceAll_seenRange cx np owner typ d st1 cached
        revert first frame1 seen1
        cases replaceAll cx np owner typ d st1 with
        | mk left st2 =>
          intro first frame1 seen1
          have second := ihb (d+1) st2 first.1 seen1
            (parts.2.mono (fun _ known => known.frame (frame.trans frame1)))
          have frame2 := replaceAll_frame cx np owner body (d+1) st2
          revert second frame2
          cases replaceAll cx np owner body (d+1) st2 with
          | mk right st3 =>
            intro second frame2
            refine ⟨second.1,?_⟩
            have leftScope := first.2.mono (fun _ known => known.frame frame2)
            simpa [RefScope,sourceExprRefs,or_imp,forall_and] using And.intro leftScope second.2
  | letE name typ value body nonDep hash iht ihv ihb =>
    intro d st scope seen expression
    rw [replaceAll.eq_1]
    have query := replaceIfNested_scope cx np owner (.letE name typ value body nonDep hash) d st lookup scope seen parameters expression
    have frame := replaceIfNested_frame cx np owner (.letE name typ value body nonDep hash) d st
    have cached := replaceIfNested_seenRange cx np owner (.letE name typ value body nonDep hash) d st seen
    revert query frame cached
    cases replaceIfNested cx np owner (.letE name typ value body nonDep hash) d st with
    | mk result st1 =>
      intro query frame cached
      cases result with
      | some value => exact ⟨query.1,query.2 value rfl⟩
      | none =>
        dsimp only
        have parts : RefScope (RunKnown cx st) typ ∧ RefScope (RunKnown cx st) value ∧
            RefScope (RunKnown cx st) body := by
          simpa [RefScope,sourceExprRefs,or_imp,forall_and,and_assoc] using expression
        have first := iht d st1 query.1 cached (parts.1.mono (fun _ known => known.frame frame))
        have frame1 := replaceAll_frame cx np owner typ d st1
        have seen1 := replaceAll_seenRange cx np owner typ d st1 cached
        revert first frame1 seen1
        cases replaceAll cx np owner typ d st1 with
        | mk typ' st2 =>
          intro first frame1 seen1
          have second := ihv d st2 first.1 seen1
            (parts.2.1.mono (fun _ known => known.frame (frame.trans frame1)))
          have frame2 := replaceAll_frame cx np owner value d st2
          have seen2 := replaceAll_seenRange cx np owner value d st2 seen1
          revert second frame2 seen2
          cases replaceAll cx np owner value d st2 with
          | mk value' st3 =>
            intro second frame2 seen2
            have third := ihb (d+1) st3 second.1 seen2
              (parts.2.2.mono (fun _ known => known.frame (frame.trans (frame1.trans frame2))))
            have frame3 := replaceAll_frame cx np owner body (d+1) st3
            revert third frame3
            cases replaceAll cx np owner body (d+1) st3 with
            | mk body' st4 =>
              intro third frame3
              refine ⟨third.1,?_⟩
              have typeScope := first.2.mono (fun _ known => known.frame (frame2.trans frame3))
              have valueScope := second.2.mono (fun _ known => known.frame frame3)
              simpa [RefScope,sourceExprRefs,or_imp,forall_and,and_assoc] using
                And.intro typeScope (And.intro valueScope third.2)
  | proj name index body hash ih =>
    intro d st scope seen expression
    rw [replaceAll.eq_1]
    have query := replaceIfNested_scope cx np owner (.proj name index body hash) d st lookup scope seen parameters expression
    have frame := replaceIfNested_frame cx np owner (.proj name index body hash) d st
    have cached := replaceIfNested_seenRange cx np owner (.proj name index body hash) d st seen
    revert query frame cached
    cases replaceIfNested cx np owner (.proj name index body hash) d st with
    | mk result st1 =>
      intro query frame cached
      cases result with
      | some value => exact ⟨query.1,query.2 value rfl⟩
      | none =>
        dsimp only
        have parts : RunKnown cx st name ∧ RefScope (RunKnown cx st) body := by
          simpa [RefScope,sourceExprRefs,or_imp,forall_and] using expression
        have result := ih d st1 query.1 cached (parts.2.mono (fun _ known => known.frame frame))
        have bodyFrame := replaceAll_frame cx np owner body d st1
        revert result bodyFrame
        cases replaceAll cx np owner body d st1 with
        | mk body' st2 =>
          intro result bodyFrame
          refine ⟨result.1,?_⟩
          have nameScope := parts.1.frame (frame.trans bodyFrame)
          simpa [RefScope,sourceExprRefs,or_imp,forall_and] using And.intro nameScope result.2
  | mdata data body hash ih =>
    intro d st scope seen expression
    rw [replaceAll.eq_1]
    have query := replaceIfNested_scope cx np owner (.mdata data body hash) d st lookup scope seen parameters expression
    have frame := replaceIfNested_frame cx np owner (.mdata data body hash) d st
    have cached := replaceIfNested_seenRange cx np owner (.mdata data body hash) d st seen
    revert query frame cached
    cases replaceIfNested cx np owner (.mdata data body hash) d st with
    | mk result st1 =>
      intro query frame cached
      cases result with
      | some value => exact ⟨query.1,query.2 value rfl⟩
      | none =>
        dsimp only
        have bodyScope : RefScope (RunKnown cx st) body := expression
        have result := ih d st1 query.1 cached (bodyScope.mono (fun _ known => known.frame frame))
        revert result
        cases replaceAll cx np owner body d st1 with
        | mk body' st2 => intro result; exact result
  | bvar index hash =>
    intro d st scope seen expression
    rw [replaceAll.eq_1]
    have query := replaceIfNested_scope cx np owner (.bvar index hash) d st lookup scope seen parameters expression
    have frame := replaceIfNested_frame cx np owner (.bvar index hash) d st
    have cached := replaceIfNested_seenRange cx np owner (.bvar index hash) d st seen
    revert query frame cached
    cases replaceIfNested cx np owner (.bvar index hash) d st with
    | mk result st1 =>
      intro query frame cached
      cases result with
      | some value => exact ⟨query.1,query.2 value rfl⟩
      | none =>
        dsimp only
        exact ⟨query.1,expression.mono (fun _ known => known.frame frame)⟩
  | fvar name hash =>
    intro d st scope seen expression
    rw [replaceAll.eq_1]
    have query := replaceIfNested_scope cx np owner (.fvar name hash) d st lookup scope seen parameters expression
    have frame := replaceIfNested_frame cx np owner (.fvar name hash) d st
    have cached := replaceIfNested_seenRange cx np owner (.fvar name hash) d st seen
    revert query frame cached
    cases replaceIfNested cx np owner (.fvar name hash) d st with
    | mk result st1 =>
      intro query frame cached
      cases result with
      | some value => exact ⟨query.1,query.2 value rfl⟩
      | none =>
        dsimp only
        exact ⟨query.1,expression.mono (fun _ known => known.frame frame)⟩
  | mvar name hash =>
    intro d st scope seen expression
    rw [replaceAll.eq_1]
    have query := replaceIfNested_scope cx np owner (.mvar name hash) d st lookup scope seen parameters expression
    have frame := replaceIfNested_frame cx np owner (.mvar name hash) d st
    have cached := replaceIfNested_seenRange cx np owner (.mvar name hash) d st seen
    revert query frame cached
    cases replaceIfNested cx np owner (.mvar name hash) d st with
    | mk result st1 =>
      intro query frame cached
      cases result with
      | some value => exact ⟨query.1,query.2 value rfl⟩
      | none =>
        dsimp only
        exact ⟨query.1,expression.mono (fun _ known => known.frame frame)⟩
  | sort level hash =>
    intro d st scope seen expression
    rw [replaceAll.eq_1]
    have query := replaceIfNested_scope cx np owner (.sort level hash) d st lookup scope seen parameters expression
    have frame := replaceIfNested_frame cx np owner (.sort level hash) d st
    have cached := replaceIfNested_seenRange cx np owner (.sort level hash) d st seen
    revert query frame cached
    cases replaceIfNested cx np owner (.sort level hash) d st with
    | mk result st1 =>
      intro query frame cached
      cases result with
      | some value => exact ⟨query.1,query.2 value rfl⟩
      | none =>
        dsimp only
        exact ⟨query.1,expression.mono (fun _ known => known.frame frame)⟩
  | const name levels hash =>
    intro d st scope seen expression
    rw [replaceAll.eq_1]
    have query := replaceIfNested_scope cx np owner (.const name levels hash) d st lookup scope seen parameters expression
    have frame := replaceIfNested_frame cx np owner (.const name levels hash) d st
    have cached := replaceIfNested_seenRange cx np owner (.const name levels hash) d st seen
    revert query frame cached
    cases replaceIfNested cx np owner (.const name levels hash) d st with
    | mk result st1 =>
      intro query frame cached
      cases result with
      | some value => exact ⟨query.1,query.2 value rfl⟩
      | none =>
        dsimp only
        exact ⟨query.1,expression.mono (fun _ known => known.frame frame)⟩
  | lit literal hash =>
    intro d st scope seen expression
    rw [replaceAll.eq_1]
    have query := replaceIfNested_scope cx np owner (.lit literal hash) d st lookup scope seen parameters expression
    have frame := replaceIfNested_frame cx np owner (.lit literal hash) d st
    have cached := replaceIfNested_seenRange cx np owner (.lit literal hash) d st seen
    revert query frame cached
    cases replaceIfNested cx np owner (.lit literal hash) d st with
    | mk result st1 =>
      intro query frame cached
      cases result with
      | some value => exact ⟨query.1,query.2 value rfl⟩
      | none =>
        dsimp only
        exact ⟨query.1,expression.mono (fun _ known => known.frame frame)⟩

/-- Pointwise membership invariant for the actual array update. -/
theorem array_modify_forall {α : Type} (P : α → Prop) (values : Array α)
    (index : Nat) (update : α → α)
    (prior : ∀ value ∈ values, P value)
    (step : ∀ value, P value → P (update value)) :
    ∀ value ∈ values.modify index update, P value := by
  intro value member
  obtain ⟨j,bound,equal⟩ := Array.mem_iff_getElem.mp member
  have found : (values.modify index update)[j]? = some value := by
    rw [Array.getElem?_eq_getElem bound,equal]
  rw [Array.getElem?_modify] at found
  split at found
  · cases old : values[j]? with
    | none => simp [old] at found
    | some original =>
      simp only [old,Option.map_some,Option.some.injEq] at found
      rw [← found]
      exact step original (prior original (Array.mem_of_getElem? old))
  · exact prior value (Array.mem_of_getElem? found)

/-- Rewriting the actual selected constructor preserves every queue member's
reference scope, including the parameter binders put back around the body. -/
theorem walkCtor_scope (cx : XCtx) (qi ci : Nat) (st : XSt)
    (lookup : cx.ind? = IndView.ofConst? cx.source.get?)
    (parameters : ∀ b ∈ cx.paramBinders, BinderScope (RunReach cx) b)
    (scope : ExpansionScope cx st) (seen : SeenRange st) :
    ExpansionScope cx (walkCtor cx qi ci st) := by
  unfold walkCtor
  split
  · exact scope
  · rename_i member foundMember
    split
    · exact scope
    · rename_i ctor foundCtor
      have constructorScope := (scope.members member (Array.mem_of_getElem? foundMember)).2
        ctor (Array.mem_of_getElem? foundCtor)
      have peeled := constructorScope.peelForalls cx.nParams #[] (by simp)
      generalize telescope : peelForalls cx.nParams ctor.typ #[] = pair at peeled ⊢
      obtain ⟨binders,body⟩ := pair
      dsimp only at peeled ⊢
      have rewritten := replaceAll_scope cx binders.size
        member.sourceOwner lookup parameters body 0 st scope seen peeled.1
      have frame := replaceAll_frame cx binders.size member.sourceOwner body 0 st
      revert rewritten frame
      cases replaceAll cx binders.size member.sourceOwner body 0 st with
      | mk body' next =>
        intro rewritten frame
        constructor
        · change ∀ current ∈ next.types.modify qi (fun m =>
            { m with ctors := m.ctors.modify ci (fun c => { c with typ := mkForalls binders body' }) }),
              MemberScope (RunKnown cx next) current
          refine array_modify_forall (MemberScope (RunKnown cx next)) next.types qi _
            rewritten.1.members ?_
          intro current currentScope
          constructor
          · exact currentScope.1
          · change ∀ ctor ∈ current.ctors.modify ci (fun c => { c with typ := mkForalls binders body' }),
              RefScope (RunKnown cx next) ctor.typ
            refine array_modify_forall (fun ctor : XCtor => RefScope (RunKnown cx next) ctor.typ)
              current.ctors ci _ currentScope.2 ?_
            intro old oldScope
            apply rewritten.2.mkForalls
            intro binder foundBinder
            exact (show RefScope (RunKnown cx st) binder.2.1 from peeled.2 binder foundBinder).mono
              (fun _ known => known.frame frame)
        · exact rewritten.1.sourceCache

/-- Every successful actual queue run preserves source/member scope. Both
key errors and the fuel boundary keep their original failure behavior. -/
theorem walkQueue_scope (cx : XCtx)
    (lookup : cx.ind? = IndView.ofConst? cx.source.get?)
    (parameters : ∀ b ∈ cx.paramBinders, BinderScope (RunReach cx) b) :
    ∀ (fuel qi : Nat) (st final : XSt), ExpansionScope cx st → SeenRange st →
      walkQueue cx fuel qi st = .ok final → ExpansionScope cx final
  | 0,qi,st,final,scope,seen,run => by
    rw [walkQueue.eq_1] at run
    split at run
    · cases run
    · split at run
      · cases run
      · cases except_pure_ok run
        exact scope
  | fuel+1,qi,st,final,scope,seen,run => by
    rw [walkQueue.eq_2] at run
    split at run
    · cases run
    · split at run
      · cases except_pure_ok run
        exact scope
      · rename_i member found
        have step : ExpansionScope cx
            ((List.range member.ctors.size).foldl (fun s ci => walkCtor cx qi ci s) st) ∧
            SeenRange ((List.range member.ctors.size).foldl (fun s ci => walkCtor cx qi ci s) st) := by
          refine list_foldl_inv (fun s => ExpansionScope cx s ∧ SeenRange s)
            _ ?_ _ _ ⟨scope,seen⟩
          intro current index invariant
          exact ⟨walkCtor_scope cx qi index current lookup parameters invariant.1 invariant.2,
            walkCtor_seenRange cx qi index current invariant.2⟩
        exact walkQueue_scope cx lookup parameters fuel (qi+1) _ final step.1 step.2 run


/-- The actual initialized queue discharges both internal reference invariants.
The source and alias facts are supplied by `expand_initialization` below. -/
theorem initializedQueue_referenceInvariant (cx : XCtx)
    (lookup : cx.ind? = IndView.ofConst? cx.source.get?)
    (parameters : ∀ b ∈ cx.paramBinders, BinderScope (RunReach cx) b)
    (ordered : Array Name) (members : ∀ name ∈ ordered, RunReach cx name)
    (aliases : Std.HashMap Name Name)
    (range : ∀ query value, aliases.get? query = some value → RunReach cx value)
    {initial final : XSt} (initialRun : initialMembers cx ordered aliases = .ok initial)
    (queueRun : walkQueue cx expansionBound 0 initial = .ok final) :
    ExpansionReferenceInvariant cx final := by
  have start := initialize_referenceInvariant lookup ordered members aliases range initialRun
  have scope := walkQueue_scope cx lookup parameters expansionBound 0 initial final
    start.scope start.seen queueRun
  exact ⟨scope.members,scope.sourceCache,
    walkQueue_seenRange cx expansionBound 0 initial final start.seen queueRun⟩

/-- Every successful canonical expansion has the actual scoped final queue.
Its source support, parameter binders and alias range are derived from the
real initializer; no reference, freshness or key-agreement premise is added. -/
theorem expand_referenceInvariant (source : Ix.Environment) (dedup : Dedup)
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
        ExpansionReferenceInvariant cx final ∧
        x = {
          types := final.types, auxToNested := final.auxToNested,
          auxCtorMap := final.auxCtorMap, nOriginals := initial.types.size,
          levelParams := fi.levelParams, nParams := fi.numParams,
          all0 := cx.all0, sourceNames := final.sourceNames?.getD [] } := by
  obtain ⟨first,fi,firstFound,viewFound,initial,final,initialRun,_,parameters,queueRun,output⟩ :=
    expand_initialization source dedup classes groupOf keyAddr? run
  refine ⟨first,fi,firstFound,viewFound,initial,final,initialRun,queueRun,?_,output⟩
  refine initializedQueue_referenceInvariant _ rfl parameters (repsOf classes) ?_
    (aliasesOf classes) ?_ initialRun queueRun
  · intro name member
    exact SourceReach.seed (by simpa using member)
  · intro query value found
    exact SourceReach.alias_value source groupOf.blocks classes found


end Ix.CompileCert.Canon
