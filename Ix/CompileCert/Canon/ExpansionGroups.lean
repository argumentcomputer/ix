import Ix.CompileCert.Canon.ExpansionSeen

namespace Ix.CompileCert.Canon
open Ix.Compile.Canon
open Ix (Name Expr)

/-- Proof-side name for exactly one constructor iteration in nested discovery. -/
def nestedCtorStep (cx : XCtx) (sourceName auxName : Name) (view : IndView)
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

/-- The constructor loop as an exact proof-side expression. -/
def nestedCtors (cx : XCtx) (sourceName auxName : Name) (view : IndView)
    (externalParams : Nat) (levels : Array Ix.Level) (specs : Array Expr)
    (sourceNames : List Lean.Name) (st : XSt) : XSt × Array XCtor :=
  forIn (m := Id) view.ctors (st,#[])
    (nestedCtorStep cx sourceName auxName view externalParams levels specs sourceNames)

/-- These fields are literally untouched by the actual constructor loop. -/
theorem nestedCtors_fields (cx : XCtx) (sourceName auxName : Name) (view : IndView)
    (externalParams : Nat) (levels : Array Ix.Level) (specs : Array Expr)
    (sourceNames : List Lean.Name) (st : XSt) :
    let result := nestedCtors cx sourceName auxName view externalParams levels specs sourceNames st
    result.1.types = st.types ∧ result.1.typeNames = st.typeNames ∧
      result.1.sourceNames? = st.sourceNames? ∧ result.1.seen = st.seen := by
  unfold nestedCtors
  refine forIn_id_inv_array (fun q : XSt × Array XCtor =>
    q.1.types = st.types ∧ q.1.typeNames = st.typeNames ∧
      q.1.sourceNames? = st.sourceNames? ∧ q.1.seen = st.seen)
    _ ?_ _ _ ⟨rfl,rfl,rfl,rfl⟩
  intro sourceCtor q preserved
  obtain ⟨cn,ct,nf⟩ := sourceCtor
  exact preserved

/-- Instantiation, result-head rewriting and the parameter telescope add
only their actual argument references and the allocated auxiliary. -/
theorem nestedCtors_scope (cx : XCtx) (sourceName auxName : Name) (view : IndView)
    (externalParams : Nat) (levels : Array Ix.Level) (specs : Array Expr)
    (sourceNames : List Lean.Name) (st : XSt) (P : Name → Prop)
    (known : P auxName) (parameters : ∀ b ∈ cx.paramBinders, BinderScope P b)
    (arguments : ∀ e ∈ specs, RefScope P e)
    (constructors : ∀ c ∈ view.ctors, RefScope P c.2.1) :
    ∀ ctor ∈ (nestedCtors cx sourceName auxName view externalParams levels specs sourceNames st).2,
      RefScope P ctor.typ := by
  unfold nestedCtors
  refine forIn_id_inv_array_mem
    (fun q : XSt × Array XCtor => ∀ ctor ∈ q.2, RefScope P ctor.typ)
    _ _ _ (by simp) ?_
  intro sourceCtor sourceMember q previous
  obtain ⟨cn,ct,nf⟩ := sourceCtor
  intro ctor member
  change ctor ∈ q.2.push _ at member
  rcases Array.mem_push.mp member with old | rfl
  · exact previous ctor old
  · exact (((constructors (cn,ct,nf) sourceMember).substLevels view.levelParams levels).instantiatePiParams
      arguments externalParams).replaceCtorResultHead sourceName auxName known externalParams
        cx.blockLevels cx.nParams 0 |>.mkForalls parameters

/-- Exactly the class body run by `replaceIfNested`, with its captured key
context and replacement function passed as ordinary proof-side arguments. -/
def nestedClassStep (cx : XCtx) (owner : Name) (externalParams : Nat)
    (levels : Array Ix.Level) (specs : Array Expr) (original : Expr)
    (keyOf : Expr → Except String OccurrenceInput) (head : Name)
    (repl : Name → Expr) (cls : Array Name) (state : XSt × Option Expr) :
    Id (ForInStep (XSt × Option Expr)) := do
  let some name := cls[0]? | return .yield state
  let some view := cx.ind? name | return .yield state
  let st := state.1
  let sourceNames := st.sourceNames cx
  let auxName := freshFamily (st.allocatedNames ++ sourceNames) (Name.mkStr cx.all0 "_nested")
    s!"{(namePretty name).replace "." "_"}_{st.nextAuxIdx}"
  let occurrence := mkAppN (Expr.mkConst name levels) specs
  let st := { st with
    nextAuxIdx := st.nextAuxIdx + 1,
    sourceNames? := some sourceNames, allocatedNames := keyName auxName :: st.allocatedNames,
    auxToNested := st.auxToNested.insert auxName occurrence }
  let st := match cx.dedup with
    | .compiler => if st.seen.contains original then st else
        { st with seen := st.seen.insert original auxName }
    | .lean => cls.foldl (init := st) fun st alias =>
        match keyOf (mkAppN (Expr.mkConst alias levels) specs) with
        | .error message => { st with keyError := st.keyError.or (some message) }
        | .ok key => if st.seen.contains key then st else { st with seen := st.seen.insert key auxName }
  let typ := mkForalls cx.paramBinders
    (instantiatePiParams (substLevels view.levelParams levels view.type) externalParams specs)
  let result := nestedCtors cx name auxName view externalParams levels specs sourceNames st
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

/-- Definitional connection to the real runtime entry. The proof-side loop
names do not introduce an alternate algorithm or an execution premise. -/
theorem replaceIfNested_group_def (cx : XCtx) (np : Nat) (owner : Name)
    (e : Expr) (depth : Nat) (st : XSt) :
    replaceIfNested cx np owner e depth st = (Id.run do
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
          (nestedClassStep cx owner externalParams levels specs original keyOf name repl)
        return (result.2,result.1)) := by
  rfl

end Ix.CompileCert.Canon

