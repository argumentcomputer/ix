import Ix.CompileCert.Canon.ExpansionGroups

namespace Ix.CompileCert.Canon
open Ix.Compile.Canon
open Ix (Name Expr)

/-- Constructor allocation preserves the actual queue/allocation frame. -/
theorem nestedCtors_frame (cx : XCtx) (sourceName auxName : Name) (view : IndView)
    (externalParams : Nat) (levels : Array Ix.Level) (specs : Array Expr)
    (sourceNames : List Lean.Name) (st : XSt) :
    ExpansionFrame cx st
      (nestedCtors cx sourceName auxName view externalParams levels specs sourceNames st).1 := by
  unfold nestedCtors
  refine forIn_id_inv_array (fun q : XSt × Array XCtor => ExpansionFrame cx st q.1)
    _ ?_ _ _ (ExpansionFrame.refl cx st)
  intro sourceCtor q frame
  obtain ⟨cn,ct,nf⟩ := sourceCtor
  exact frame.trans (ExpansionFrame.constructor cx q.1 _)

/-- The constructor loop changes no queued member, queue identity or source
cache, so the real member-scope invariant survives its allocation work. -/
theorem nestedCtors_expansionScope (cx : XCtx) (sourceName auxName : Name) (view : IndView)
    (externalParams : Nat) (levels : Array Ix.Level) (specs : Array Expr)
    (sourceNames : List Lean.Name) (st : XSt) (scope : ExpansionScope cx st) :
    ExpansionScope cx
      (nestedCtors cx sourceName auxName view externalParams levels specs sourceNames st).1 := by
  have fields := nestedCtors_fields cx sourceName auxName view externalParams levels specs sourceNames st
  constructor
  · intro member found
    rw [fields.1] at found
    have previous := scope.members member found
    exact previous.mono (fun _ known =>
      known.frame (nestedCtors_frame cx sourceName auxName view externalParams levels specs sourceNames st))
  · rcases scope.sourceCache with empty | full
    · exact Or.inl (fields.2.2.1.trans empty)
    · exact Or.inr (fields.2.2.1.trans full)

/-- The exact class step retains earlier queue identities and allocation
history, including its skipped classes and both dedup branches. -/
theorem nestedClassStep_frame (cx : XCtx) (owner : Name) (externalParams : Nat)
    (levels : Array Ix.Level) (specs : Array Expr) (original : Expr)
    (keyOf : Expr → Except String OccurrenceInput) (head : Name)
    (repl : Name → Expr) (cls : Array Name) (state next : XSt × Option Expr)
    (run : nestedClassStep cx owner externalParams levels specs original keyOf head repl cls state =
      .yield next) : ExpansionFrame cx state.1 next.1 := by
  unfold nestedClassStep at run
  repeat' split at run
  all_goals
    cases run
    first
    | exact ExpansionFrame.refl cx state.1
    | (refine ExpansionFrame.trans ?_ (ExpansionFrame.push cx _ _)
       refine ExpansionFrame.trans ?_ (nestedCtors_frame cx _ _ _ _ _ _ _ _)
       first
       | exact ExpansionFrame.reserve cx state.1 _
       | (split <;> exact ExpansionFrame.reserve cx state.1 _)
       | (refine array_foldl_inv (fun q : XSt => ExpansionFrame cx state.1 q)
           _ ?_ _ _ ?_
          · intro q alias previous
            try dsimp only
            repeat' first | exact previous | split
          · exact ExpansionFrame.reserve cx state.1 _))

/-- Proof-side name for the exact nested-cache registration expression. -/
def nestedSeen (dedup : Dedup) (original : Expr)
    (keyOf : Name → Except String OccurrenceInput) (cls : Array Name)
    (aux : Name) (st : XSt) : XSt :=
  match dedup with
  | .compiler => if st.seen.contains original then st else
      { st with seen := st.seen.insert original aux }
  | .lean => cls.foldl (init := st) fun st alias =>
      match keyOf alias with
      | .error message => { st with keyError := st.keyError.or (some message) }
      | .ok key => if st.seen.contains key then st else { st with seen := st.seen.insert key aux }

theorem nestedSeen_fields (dedup : Dedup) (original : Expr)
    (keyOf : Name → Except String OccurrenceInput) (cls : Array Name)
    (aux : Name) (st : XSt) :
    let result := nestedSeen dedup original keyOf cls aux st
    result.types = st.types ∧ result.typeNames = st.typeNames ∧
      result.sourceNames? = st.sourceNames? := by
  unfold nestedSeen
  split
  · split <;> exact ⟨rfl,rfl,rfl⟩
  · refine array_foldl_inv (fun q : XSt => q.types = st.types ∧
      q.typeNames = st.typeNames ∧ q.sourceNames? = st.sourceNames?) _ ?_ _ _ ⟨rfl,rfl,rfl⟩
    intro q alias previous
    repeat' first | exact previous | split

theorem nestedSeen_expansionScope {cx : XCtx} (dedup : Dedup) (original : Expr)
    (keyOf : Name → Except String OccurrenceInput) (cls : Array Name)
    (aux : Name) (st : XSt) (scope : ExpansionScope cx st) :
    ExpansionScope cx (nestedSeen dedup original keyOf cls aux st) := by
  have fields := nestedSeen_fields dedup original keyOf cls aux st
  constructor
  · intro member found
    rw [fields.1] at found
    apply (scope.members member found).mono
    intro name known
    rcases known with source | queued
    · exact Or.inl source
    · exact Or.inr (by simpa only [fields.2.1] using queued)
  · rcases scope.sourceCache with empty | full
    · exact Or.inl (fields.2.2.trans empty)
    · exact Or.inr (fields.2.2.trans full)

/-- Every newly appended member uses only the actual source closure, earlier
queued identities, and its newly allocated identity. The hypotheses here are
internal loop invariants supplied by the actual expansion initializer/query. -/
theorem nestedClassStep_expansionScope (cx : XCtx) (owner : Name) (externalParams : Nat)
    (levels : Array Ix.Level) (specs : Array Expr) (original : Expr)
    (keyOf : Expr → Except String OccurrenceInput) (head : Name)
    (repl : Name → Expr) (cls : Array Name) (state next : XSt × Option Expr)
    (lookup : cx.ind? = IndView.ofConst? cx.source.get?)
    (scope : ExpansionScope cx state.1)
    (parameters : ∀ b ∈ cx.paramBinders, BinderScope (RunReach cx) b)
    (arguments : ∀ e ∈ specs, RefScope (RunKnown cx state.1) e)
    (reached : ∀ name ∈ cls, RunReach cx name)
    (run : nestedClassStep cx owner externalParams levels specs original keyOf head repl cls state =
      .yield next) : ExpansionScope cx next.1 := by
  have frame := nestedClassStep_frame cx owner externalParams levels specs original keyOf head repl cls state next run
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
      rw [sameState] at frame ⊢
      have preparedScope : ExpansionScope cx prepared := by
        constructor
        · exact scope.members
        · exact Or.inr (congrArg some scope.sourceNames)
      have registeredScope := nestedSeen_expansionScope cx.dedup original
        (fun alias => keyOf (mkAppN (Expr.mkConst alias levels) specs)) cls auxName prepared preparedScope
      have resultScope := nestedCtors_expansionScope cx name auxName view externalParams levels specs
        sourceNames registered registeredScope
      apply resultScope.push member
      have actual : IndView.ofConst? cx.source.get? name = some view := by simpa [lookup] using found
      have nameReached := reached name (Array.mem_of_getElem? chosen)
      have typeScope : RefScope (RunReach cx) view.type := by
        obtain ⟨v,record,-,sourceType,-,-⟩ := IndView.sourceInfo actual
        rw [sourceType]
        exact nameReached.type_scope record
      have params : ∀ b ∈ cx.paramBinders, BinderScope (RunKnown cx (result.1.push member)) b := by
        intro b foundBinder
        exact (show RefScope (RunReach cx) b.2.1 from parameters b foundBinder).mono
          (fun _ h => Or.inl h)
      have args : ∀ e ∈ specs, RefScope (RunKnown cx (result.1.push member)) e :=
        fun e foundArg => (arguments e foundArg).mono (fun _ known => known.frame frame)
      constructor
      · exact (((typeScope.mono (fun _ h => Or.inl h)).substLevels view.levelParams levels).instantiatePiParams
          args externalParams).mkForalls params
      · apply nestedCtors_scope cx name auxName view externalParams levels specs sourceNames registered
          (RunKnown cx (result.1.push member)) (RunKnown.pushed cx result.1 member) params args
        intro ctor foundCtor
        exact (nameReached.viewCtor actual foundCtor).2.1.mono (fun _ h => Or.inl h)
    · cases run
      exact scope
  · cases run
    exact scope

end Ix.CompileCert.Canon

