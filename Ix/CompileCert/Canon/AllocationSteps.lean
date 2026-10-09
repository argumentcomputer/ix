import Ix.CompileCert.Canon.CoreDiscovery
import Ix.CompileCert.Canon.FreshNames

/-!
UNCOMPILED additive proof draft over the accepted callback-generic core.
This file names the actual class/constructor operations and records their
allocation events. It does not replace runtime code or add a caller premise.
-/

namespace Ix.CompileCert.Canon.ExpansionHistory

open Ix.Compile.Canon
open Ix (Name Expr)

/-- An internal cache invariant, derived from the empty initializer. -/
def CacheCorrect (cx : ExpansionCore.Ctx) (st : XSt) : Prop :=
  st.sourceNames? = none ∨ st.sourceNames? = some (cx.protect ())

theorem sourceNames_eq (cx : ExpansionCore.Ctx) (st : XSt)
    (cache : CacheCorrect cx st) : ExpansionCore.sourceNames cx st = cx.protect () := by
  rcases cache with empty | populated
  · simp only [ExpansionCore.sourceNames, empty]
  · simp only [ExpansionCore.sourceNames, populated]

/-- Exactly the captured alias-registration fragment. Its errors and insertion
order are retained, independently of any representation of the callbacks. -/
def register (dedup : Dedup) (cls : Array Name) (original : Expr)
    (keyOf : Expr → Except String OccurrenceInput) (levels : Array Ix.Level)
    (specs : Array Expr) (aux : Name) (st : XSt) : XSt :=
  match dedup with
  | .compiler => if st.seen.contains original then st else
      { st with seen := st.seen.insert original aux }
  | .lean => cls.foldl (init := st) fun st alias =>
      match keyOf (mkAppN (Expr.mkConst alias levels) specs) with
      | .error message => { st with keyError := st.keyError.or (some message) }
      | .ok key => if st.seen.contains key then st else
          { st with seen := st.seen.insert key aux }

theorem register_fields (dedup : Dedup) (cls : Array Name) (original : Expr)
    (keyOf : Expr → Except String OccurrenceInput) (levels : Array Ix.Level)
    (specs : Array Expr) (aux : Name) (st : XSt) :
    let result := register dedup cls original keyOf levels specs aux st
    result.types = st.types ∧ result.nextAuxIdx = st.nextAuxIdx ∧
      result.sourceNames? = st.sourceNames? ∧
      result.allocatedNames = st.allocatedNames ∧
      result.allocatedCtorRoots = st.allocatedCtorRoots := by
  dsimp only
  cases dedup with
  | compiler =>
    dsimp only [register]
    split <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  | lean =>
    dsimp only [register]
    refine array_foldl_inv (fun q : XSt =>
      q.types = st.types ∧ q.nextAuxIdx = st.nextAuxIdx ∧
        q.sourceNames? = st.sourceNames? ∧
        q.allocatedNames = st.allocatedNames ∧
        q.allocatedCtorRoots = st.allocatedCtorRoots) _ ?_ _ _ ⟨rfl,rfl,rfl,rfl,rfl⟩
    intro q alias preserved
    repeat' (first | exact preserved | split)

/-- The actual constructor allocation body, with the same fresh-name inputs. -/
def ctorStep (cx : ExpansionCore.Ctx) (sourceName auxName : Name) (view : IndView)
    (externalParams : Nat) (levels : Array Ix.Level) (specs : Array Expr)
    (sourceNames : List Lean.Name) (sourceCtor : Name × Expr × Nat)
    (state : XSt × Array XCtor) : Id (ForInStep (XSt × Array XCtor)) := do
  let (cn,ct,nf) := sourceCtor
  let st := state.1
  let ctors := state.2
  let candidate := nameReplacePrefix cn sourceName auxName
  let auxCtorName := freshCtorFamily (st.allocatedNames ++ sourceNames)
    auxName candidate ctors.size st.allocatedCtorRoots
  let typ := instantiatePiParams (substLevels view.levelParams levels ct) externalParams specs
  let typ := replaceCtorResultHead sourceName auxName externalParams cx.blockLevels cx.nParams typ 0
  let st := { st with
    auxCtorMap := st.auxCtorMap.insert auxCtorName (cn,auxName)
    allocatedNames := keyName auxCtorName :: st.allocatedNames
    allocatedCtorRoots := keyName auxCtorName :: st.allocatedCtorRoots }
  return .yield (st,ctors.push {
    name := auxCtorName, typ := mkForalls cx.paramBinders typ, nFields := nf })

def ctors (cx : ExpansionCore.Ctx) (sourceName auxName : Name) (view : IndView)
    (externalParams : Nat) (levels : Array Ix.Level) (specs : Array Expr)
    (sourceNames : List Lean.Name) (st : XSt) : XSt × Array XCtor :=
  forIn (m := Id) view.ctors (st,#[])
    (ctorStep cx sourceName auxName view externalParams levels specs sourceNames)

theorem ctors_fields (cx : ExpansionCore.Ctx) (sourceName auxName : Name) (view : IndView)
    (externalParams : Nat) (levels : Array Ix.Level) (specs : Array Expr)
    (sourceNames : List Lean.Name) (st : XSt) :
    let result := ctors cx sourceName auxName view externalParams levels specs sourceNames st
    result.1.types = st.types ∧ result.1.nextAuxIdx = st.nextAuxIdx ∧
      result.1.sourceNames? = st.sourceNames? := by
  unfold ctors
  refine forIn_id_inv_array (fun q : XSt × Array XCtor =>
    q.1.types = st.types ∧ q.1.nextAuxIdx = st.nextAuxIdx ∧
      q.1.sourceNames? = st.sourceNames?) _ ?_ _ _ ⟨rfl,rfl,rfl⟩
  intro sourceCtor q preserved
  obtain ⟨cn,ct,nf⟩ := sourceCtor
  exact preserved

/-- One exact class call from the captured query context. -/
def classStep (cx : ExpansionCore.Ctx) (owner : Name) (externalParams : Nat)
    (levels : Array Ix.Level) (specs : Array Expr) (original : Expr)
    (keyOf : Expr → Except String OccurrenceInput) (head : Name)
    (repl : Name → Expr) (cls : Array Name) (state : XSt × Option Expr) :
    Id (ForInStep (XSt × Option Expr)) := do
  let some name := cls[0]? | return .yield state
  let some view := cx.ind? name | return .yield state
  let st := state.1
  let sourceNames := ExpansionCore.sourceNames cx st
  let auxName := auxNameOf cx.all0 name st.nextAuxIdx (st.allocatedNames ++ sourceNames)
  let occurrence := mkAppN (Expr.mkConst name levels) specs
  let st := { st with
    nextAuxIdx := st.nextAuxIdx + 1,
    sourceNames? := some sourceNames, allocatedNames := keyName auxName :: st.allocatedNames,
    auxToNested := st.auxToNested.insert auxName occurrence }
  let st := register cx.dedup cls original keyOf levels specs auxName st
  let typ := mkForalls cx.paramBinders
    (instantiatePiParams (substLevels view.levelParams levels view.type) externalParams specs)
  let result := ctors cx name auxName view externalParams levels specs sourceNames st
  if cls.contains head then
    return .yield (result.1.push {
        name := auxName, sourceOwner := owner,
        typ, ctors := result.2, nParams := cx.nParams, nIndices := view.numIndices },
      some (repl auxName))
  else
    return .yield (result.1.push {
        name := auxName, sourceOwner := owner,
        typ, ctors := result.2, nParams := cx.nParams, nIndices := view.numIndices },
      state.2)

/-- Definitional connection to the actual generic query. Captured key context,
all early returns, every error and complete returned state remain explicit. -/
theorem replaceIfNested_class_def (cx : ExpansionCore.Ctx) (np : Nat) (owner : Name)
    (e : Expr) (depth : Nat) (st : XSt) :
    ExpansionCore.replaceIfNested cx np owner e depth st = (Id.run do
      let (head,args) := getAppFnArgs e
      let .const name levels _ := head | return (none,st)
      if st.typeNames.contains name then return (none,st)
      let some external := cx.ind? name | return (none,st)
      let externalParams := external.numParams
      if args.size < externalParams then return (none,st)
      let ps := args.extract 0 externalParams
      if !ps.any (mentionsName st.typeNames.contains) then return (none,st)
      if !ps.all (looseAtLeast · depth) then return (none,st)
      let specs := ps.map (lowerLoose · depth)
      let original := mkAppN (Expr.mkConst name levels) specs
      let repl := fun aux => mkAppN
        (mkAppN (Expr.mkConst aux cx.blockLevels) (paramArgs np depth))
        (args.extract externalParams args.size)
      let names := st.typeNames
      let keyOf := fun expression => match cx.keyAddr? with
        | some addr => addrOccurrence cx.levelParams addr names.contains expression
        | none => .ok (sourceOccurrence expression)
      match keyOf original with
      | .error message => return (none,{st with keyError := st.keyError.or (some message)})
      | .ok key =>
        if let some aux := st.seen.get? key then return (some (repl aux),st)
        let result ← forIn (m := Id) (cx.groupOf external) (st,none)
          (classStep cx owner externalParams levels specs original keyOf name repl)
        return (result.2,result.1)) := by
  rfl

/-- An event contains the real full pre-state and exact class-call arguments.
The two lookup proofs assert that this call allocates, rather than skips. -/
structure Event (cx : ExpansionCore.Ctx) where
  owner : Name
  externalParams : Nat
  levels : Array Ix.Level
  specs : Array Expr
  original : Expr
  keyOf : Expr → Except String OccurrenceInput
  head : Name
  repl : Name → Expr
  cls : Array Name
  before : XSt
  oldResult : Option Expr
  sourceName : Name
  view : IndView
  first : cls[0]? = some sourceName
  found : cx.ind? sourceName = some view
  cache : CacheCorrect cx before

def Event.after {cx : ExpansionCore.Ctx} (event : Event cx) : XSt :=
  (classStep cx event.owner event.externalParams event.levels event.specs
    event.original event.keyOf event.head event.repl event.cls
    (event.before,event.oldResult)).value.1

def Event.name {cx : ExpansionCore.Ctx} (event : Event cx) : Name :=
  auxNameOf cx.all0 event.sourceName event.before.nextAuxIdx
    (event.before.allocatedNames ++ cx.protect ())

/-- The naming argument is fixed by this event's pre-state and the exact
protection thunk. It is not an existentially chosen forbidden-name list. -/
theorem Event.after_fields {cx : ExpansionCore.Ctx} (event : Event cx) :
    skel event.after = skel event.before ++ [(event.name,event.owner)] ∧
      event.after.nextAuxIdx = event.before.nextAuxIdx + 1 ∧
      event.after.sourceNames? = some (cx.protect ()) := by
  have cache := sourceNames_eq cx event.before event.cache
  have yielded (value : XSt × Option Expr) :
      (pure (.yield value) : Id (ForInStep (XSt × Option Expr))).value = value := rfl
  unfold Event.after classStep
  rw [event.first]
  dsimp only
  rw [event.found]
  dsimp only
  simp only [cache]
  have registered := register_fields cx.dedup event.cls event.original event.keyOf
    event.levels event.specs event.name
    { event.before with
      nextAuxIdx := event.before.nextAuxIdx + 1,
      sourceNames? := some (cx.protect ()),
      allocatedNames := keyName event.name :: event.before.allocatedNames,
      auxToNested := event.before.auxToNested.insert event.name
        (mkAppN (Expr.mkConst event.sourceName event.levels) event.specs) }
  have constructed := ctors_fields cx event.sourceName event.name event.view
    event.externalParams event.levels event.specs (cx.protect ())
    (register cx.dedup event.cls event.original event.keyOf event.levels event.specs event.name
      { event.before with
        nextAuxIdx := event.before.nextAuxIdx + 1,
        sourceNames? := some (cx.protect ()),
        allocatedNames := keyName event.name :: event.before.allocatedNames,
        auxToNested := event.before.auxToNested.insert event.name
          (mkAppN (Expr.mkConst event.sourceName event.levels) event.specs) })
  dsimp only [Event.name] at registered constructed
  split <;> simp only [yielded] <;> refine ⟨?_, ?_, ?_⟩
  all_goals first
    | exact constructed.2.1.trans registered.2.1
    | exact constructed.2.2.trans registered.2.2.1
    | (unfold skel XSt.push
       rw [Array.toList_push, List.map_append, constructed.1, registered.1]
       rfl)

theorem Event.sourceFree {cx : ExpansionCore.Ctx} (event : Event cx)
    (name : Lean.Name) (member : name ∈ cx.protect ()) :
    (keyName event.name).isPrefixOf name = false := by
  exact freshFamily_free _ _ _ name (List.mem_append.mpr (.inr member))

theorem Event.previousFree {cx : ExpansionCore.Ctx} (event : Event cx)
    (name : Lean.Name) (member : name ∈ event.before.allocatedNames) :
    (keyName event.name).isPrefixOf name = false := by
  exact freshFamily_free _ _ _ name (List.mem_append.mpr (.inl member))

/-- A projection of the actual allocation history: exact allocating class
calls, key-error updates and constructor-payload rewrites. The latter two have
no allocation event. It is not a stand-alone semantics for query eligibility. -/
inductive History (cx : ExpansionCore.Ctx) : XSt → List (Event cx) → XSt → Prop where
  | refl (st : XSt) : History cx st [] st
  | keyError (st : XSt) (err : Option String) :
      History cx st [] { st with keyError := err }
  | ctorType (st : XSt) (qi ci : Nat) (typ : Expr) :
      History cx st [] { st with types := st.types.modify qi fun m =>
        { m with ctors := m.ctors.modify ci fun c => { c with typ } } }
  | allocation (event : Event cx) : History cx event.before [event] event.after
  | trans {a b c : XSt} {left right : List (Event cx)} :
      History cx a left b → History cx b right c → History cx a (left ++ right) c

theorem History.cache {cx : ExpansionCore.Ctx} {a b : XSt} {events : List (Event cx)}
    (run : History cx a events b) (initial : CacheCorrect cx a) : CacheCorrect cx b := by
  revert initial
  induction run with
  | refl => intro initial; exact initial
  | keyError => intro initial; exact initial
  | ctorType => intro initial; exact initial
  | allocation event => intro _; exact .inr event.after_fields.2.2
  | trans left right ihl ihr => intro initial; exact ihr (ihl initial)

theorem History.fields {cx : ExpansionCore.Ctx} {a b : XSt} {events : List (Event cx)}
    (run : History cx a events b) :
    skel b = skel a ++ events.map (fun event => (event.name,event.owner)) ∧
      b.nextAuxIdx = a.nextAuxIdx + events.length := by
  induction run with
  | refl => simp
  | keyError => simp [skel]
  | ctorType st qi ci typ =>
    constructor
    · simpa only [List.map_nil, List.append_nil, skel] using
        skel_modify st qi (fun m => {m with ctors := m.ctors.modify ci fun c => {c with typ}})
          (fun _ => ⟨rfl,rfl⟩)
    · rfl
  | allocation event => exact ⟨event.after_fields.1,event.after_fields.2.1⟩
  | trans left right ihl ihr =>
    constructor
    · rw [ihr.1, ihl.1, List.map_append, List.append_assoc]
    · rw [ihr.2, ihl.2, List.length_append, Nat.add_assoc]

theorem History.index {cx : ExpansionCore.Ctx} {a b : XSt} {events : List (Event cx)}
    (run : History cx a events b) : ∀ k event, events[k]? = some event →
      event.before.nextAuxIdx = a.nextAuxIdx + k := by
  induction run with
  | refl => intro k event found; simp at found
  | keyError => intro k event found; simp at found
  | ctorType => intro k event found; simp at found
  | allocation original =>
    intro k event found
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at found
      subst event
      rfl
    | succ k => simp at found
  | @trans a b c left right first second ihl ihr =>
    intro k event found
    by_cases lower : k < left.length
    · rw [List.getElem?_append_left lower] at found
      exact ihl k event found
    · rw [List.getElem?_append_right (Nat.le_of_not_lt lower)] at found
      rw [ihr _ event found, first.fields.2]
      omega

/-- Histories compose without dropping their ordered allocation events. -/
def Runs (cx : ExpansionCore.Ctx) (a b : XSt) : Prop := ∃ events, History cx a events b

theorem Runs.refl (cx : ExpansionCore.Ctx) (st : XSt) : Runs cx st st :=
  ⟨[], .refl st⟩

theorem Runs.keyError (cx : ExpansionCore.Ctx) (st : XSt) (err : Option String) :
    Runs cx st {st with keyError := err} := ⟨[], .keyError st err⟩

theorem Runs.ctorType (cx : ExpansionCore.Ctx) (st : XSt) (qi ci : Nat) (typ : Expr) :
    Runs cx st { st with types := st.types.modify qi fun m =>
      { m with ctors := m.ctors.modify ci fun c => { c with typ } } } :=
  ⟨[], .ctorType st qi ci typ⟩

theorem Runs.trans {cx : ExpansionCore.Ctx} {a b c : XSt}
    (left : Runs cx a b) (right : Runs cx b c) : Runs cx a c := by
  obtain ⟨l,hl⟩ := left
  obtain ⟨r,hr⟩ := right
  exact ⟨l ++ r,.trans hl hr⟩

theorem Runs.cache {cx : ExpansionCore.Ctx} {a b : XSt}
    (run : Runs cx a b) (cache : CacheCorrect cx a) : CacheCorrect cx b := by
  obtain ⟨events,history⟩ := run
  exact history.cache cache

theorem classStep_history (cx : ExpansionCore.Ctx) (owner : Name) (externalParams : Nat)
    (levels : Array Ix.Level) (specs : Array Expr) (original : Expr)
    (keyOf : Expr → Except String OccurrenceInput) (head : Name)
    (repl : Name → Expr) (cls : Array Name) (state : XSt × Option Expr)
    (cache : CacheCorrect cx state.1) :
    Runs cx state.1 (classStep cx owner externalParams levels specs original keyOf
      head repl cls state).value.1 := by
  have yielded (value : XSt × Option Expr) :
      (pure (.yield value) : Id (ForInStep (XSt × Option Expr))).value = value := rfl
  cases first : cls[0]? with
  | none => simpa only [classStep, first, yielded] using Runs.refl cx state.1
  | some sourceName =>
    cases found : cx.ind? sourceName with
    | none => simpa only [classStep, first, found, yielded] using Runs.refl cx state.1
    | some view =>
      let event : Event cx := {
        owner := owner, externalParams := externalParams, levels := levels,
        specs := specs, original := original, keyOf := keyOf, head := head,
        repl := repl, cls := cls, before := state.1, oldResult := state.2,
        sourceName := sourceName, view := view, first := first, found := found, cache := cache }
      exact ⟨[event],.allocation event⟩

end Ix.CompileCert.Canon.ExpansionHistory
