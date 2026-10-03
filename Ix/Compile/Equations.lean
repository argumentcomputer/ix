/-
  Unfolding equations for compiled closures.

  Lean's code generator never compiles kernel recursion (`brecOn`, `WellFounded.fix`);
  it compiles an unchecked `_unsafe_rec` twin. A certified consumer instead compiles
  the right-hand side of the kernel-checked unfolding theorem `f.eq_def`, which states
  `f xs = body` with direct recursive calls. Lean realizes these theorems lazily, so a
  closure export must realize them before computing its dependency closure.
-/
module
public import Lean.Meta.Eqns
public import Lean.Meta.LetToHave
public import Lean.Elab.PreDefinition.Structural.Eqns
public import Lean.Elab.PreDefinition.WF.Eqns
public import Lean.Elab.PreDefinition.PartialFixpoint.Eqns
public import Ix.EnvScope
public import Ix.Compile.SourceContract.Registry

public section

namespace Ix.Compile.Equations

open Lean Meta

/-- A header input contract of a definition, carried onto the same position of
its unfolding equation's statement (R1 amendment). -/
structure CarriedContract where
  position : Nat
  binder : Lean.Name
  uses : Ixon.Uses
  value : Ixon.ValueContract
  deriving Inhabited, Repr, BEq

/-- A recursive definition and its realized unfolding theorem. -/
structure Association where
  definition : Lean.Name
  equation : Lean.Name
  /-- The definition's header input contracts that the equation's statement
  carries, by telescope position. -/
  contracts : Array CarriedContract := #[]
  deriving Inhabited, Repr, BEq

/-- The statement of the unfolding theorem Lean generates for `name` from the
pre-definition `value` (universe parameters `levels`): `∀ xs, name xs = body`
where `value = fun xs => body`, with `let`s turned into `have`s, exactly as
`Structural.mkUnfoldEq`, `WF.mkUnfoldEq`/`mkBinaryUnfoldEq`,
`PartialFixpoint.mkUnfoldEq` and (for a non-recursive definition,
`cleanup := true`) `mkSimpleEqThm` state it. -/
def unfoldStatement (name : Lean.Name) (levels : List Lean.Name) (value : Lean.Expr)
    (cleanup : Bool) : MetaM Lean.Expr :=
  lambdaTelescope (cleanupAnnotations := cleanup) value fun xs body => do
    let lhs := mkAppN (mkConst name (levels.map mkLevelParam)) xs
    letToHave (← mkForallFVars xs (← mkEq lhs body))

/-- Why the theorem `equation` that `getUnfoldEqnFor?` returned for `name` is
not Lean's own unfolding theorem of `name`, or `none` when it is (second
review R2-5). `getUnfoldEqnFor?` returns any constant that already bears the
reserved name `name.eq_def`, and a metaprogram can `addDecl` one past the
reserved-name check, so the name proves nothing. The statement is re-derived
instead, from the pre-definition Lean recorded when it compiled `name`'s
recursion (`Structural`/`WF`/`PartialFixpoint.eqnInfoExt`), or from `name`'s
own value when `name` is not recursive, and the theorem's statement and
universe parameters must equal it (the proof is irrelevant: any proof of
that statement certifies the same equation). The `_unary`/`_binary`/
`_mutual` auxiliary of a well-founded definition has no recorded
pre-definition; Lean adds its unfolding theorem while it elaborates the
definition (`WF.mkUnfoldEq`), so it is accepted when the definition's
well-founded record names it as its non-recursive auxiliary and the theorem
was added in the same module as the auxiliary (afterwards the name is taken,
so a later forgery cannot replace it). The records are environment state that
a metaprogram could also overwrite, so this check is defense in depth: the
resource-safety obligation is that a consumer runs a checked definition by
the bound right-hand side, fetched by its address (docs/source-contracts.md,
"Checked pairs"). -/
def notGenuine (name equation : Lean.Name) : MetaM (Option String) := do
  let env ← getEnv
  let some (.thmInfo thm) := env.find? equation
    | return some s!"`{equation}` is not a theorem"
  let some (.defnInfo info) := env.find? name
    | return some s!"`{name}` is not a definition"
  let recorded : Option (List Lean.Name × Lean.Expr) :=
    match Elab.Structural.eqnInfoExt.find? env name with
    | some i => some (i.levelParams, i.value)
    | none => match Elab.WF.eqnInfoExt.find? env name with
      | some i => some (i.levelParams, i.value)
      | none => (Elab.PartialFixpoint.eqnInfoExt.find? env name).map
          fun i => (i.levelParams, i.value)
  let mut expected := none
  if let some (levels, value) := recorded then
    expected := some (levels, ← unfoldStatement name levels value false)
  else if ← isRecursiveDefinition name then
    let auxiliary := match name with
      | .str parent _ => (Elab.WF.eqnInfoExt.find? env parent).any (·.declNameNonRec == name)
      | _ => false
    -- Lean's theorem lies in the auxiliary's module; an importer sees it
    -- through `WF.copyPrivateUnfoldTheorem`'s alias of the private original.
    let copied := match env.getModuleIdxFor? name with
      | some idx =>
        let original := mkPrivateNameCore env.allImportedModuleNames[idx.toNat]!
          (.str (privateToUserName name) "eq_def")
        match env.find? original, env.getModuleIdxFor? original with
        | some (.thmInfo o), some home =>
          home == idx && o.type == thm.type && o.levelParams == thm.levelParams &&
            thm.value == mkConst original (o.levelParams.map mkLevelParam)
        | _, _ => false
      | none => false
    if auxiliary && (env.getModuleIdxFor? equation == env.getModuleIdxFor? name || copied) then
      return none
  else
    expected := some (info.levelParams, ← unfoldStatement name info.levelParams info.value true)
  let some (levels, statement) := expected
    | return some s!"no recorded pre-definition of `{name}` to re-derive `{equation}` from"
  unless thm.levelParams == levels && thm.type == statement do
    return some s!"the statement of `{equation}` is not the unfolding of `{name}`'s \
      pre-definition"
  return none

/-- Realize `f.eq_def` for every recursive definition among `names`: structural,
well-founded (including `WellFounded.Nat.fix` fuel encodings), mutual and
`partial_fixpoint` definitions. Non-recursive definitions produce nothing.
Definitions whose equation generation throws are returned with the message, so
a caller can report them instead of silently dropping them. A theorem that is
not Lean's own unfolding theorem (`notGenuine`, second review R2-5) is not
associated: its definition is returned as a failure, `equation not genuine`. -/
def realize (env : Lean.Environment) (names : List Lean.Name)
    : IO (Lean.Environment × Array Association × Array (Lean.Name × String)) := do
  let ctx : Core.Context := { fileName := "<ix-equations>", fileMap := default, maxHeartbeats := 0 }
  let action : MetaM (Array Association × Array (Lean.Name × String)) := do
    let mut found := #[]
    let mut failed := #[]
    for name in names do
      let some (.defnInfo _) := (← getEnv).find? name | continue
      try
        if let some equation ← getUnfoldEqnFor? name then
          match ← notGenuine name equation with
          | none => found := found.push { definition := name, equation }
          | some why => failed := failed.push (name, s!"equation not genuine: {why}")
      catch error =>
        failed := failed.push (name, ← error.toMessageData.toString)
    return (found, failed)
  let ((found, failed), state) ← (action.run' {} {}).toIO ctx { env }
  return (state.env, found, failed)

/-- Close `seeds` over dependencies and over the unfolding theorems of every
recursive definition reached, until no new theorem appears. The equations' own
dependencies (matchers, and definitions their statements mention) join the
closure, and their recursive definitions are processed in turn. -/
partial def close (env : Lean.Environment) (seeds : List Lean.Name)
    : IO (Lean.Environment × List (Lean.Name × Lean.ConstantInfo) × Array Association × Array (Lean.Name × String)) :=
  loop env seeds {} #[] #[]
where
  loop (env : Lean.Environment) (seeds : List Lean.Name) (visited : Lean.NameSet)
      (found : Array Association) (failed : Array (Lean.Name × String)) :
      IO (Lean.Environment × List (Lean.Name × Lean.ConstantInfo) × Array Association × Array (Lean.Name × String)) := do
    let closed := Ix.EnvScope.collectDeps env seeds
    let pending := closed.filterMap fun (name, _) =>
      if visited.contains name then none else some name
    if pending.isEmpty then
      return (env, closed, found, failed)
    let (env, newFound, newFailed) ← realize env pending
    let visited := pending.foldl (·.insert ·) visited
    let equations := newFound.toList.map (·.equation)
    loop env (seeds ++ equations) visited (found ++ newFound) (failed ++ newFailed)

/-- The non-default input contracts of a declaration's type telescope, from its
registered or marked source contract. -/
def headerContracts (env : Lean.Environment) (info : Lean.ConstantInfo) :
    Except Ix.Compile.SourceContractError (Array CarriedContract) := do
  let input ← Ix.Compile.compileInputFromEnv env [(info.name, info)]
  let some contract := input.contracts[0]? | return #[]
  let resolved ← contract.resolve info
  let types := Ix.Compile.sourceTelescope info .type
  let mut carried := #[]
  for i in [:types.size] do
    let (site, binder) := types[i]!
    if let some b := resolved.binders.find? (·.site == site) then
      if b.uses != .many || b.value != .shared then
        carried := carried.push { position := i, binder, uses := b.uses, value := b.value }
  return carried

/-- Carry each definition's header input contracts onto its unfolding
equation (R1 amendment): the statement's binder at the same telescope position,
and the matching lambda of the proof, are registered with the same input
contract, so that transport writes them into the exported theorem. Result
contracts are not carried: the statement's arrows end in an equality, not in
the definition's result. Contracts written inside the body already reach the
statement. An equation whose telescope does not match is left unchanged and
reported. -/
def carryContracts (env : Lean.Environment) (found : Array Association) :
    Lean.Environment × Array Association × Array (Lean.Name × String) := Id.run do
  let mut env := env
  let mut result := #[]
  let mut failed := #[]
  for a in found do
    let (some definition, some equation) := (env.find? a.definition, env.find? a.equation)
      | result := result.push a
        continue
    match headerContracts env definition with
    | .error error =>
      failed := failed.push (a.definition, s!"contracts not carried: {error}")
      result := result.push a
    | .ok carried =>
      if carried.isEmpty then
        result := result.push a
        continue
      let requests := carried.map fun c =>
        ({ binder := .position c.position, uses := c.uses, value := c.value } : Ix.Compile.TelescopeContract)
      let registered : Except Ix.Compile.SourceContractError Lean.Environment := do
        let header ← Ix.Compile.SourceContract.ofTelescope equation requests
        let existing ← if Ix.Compile.sourceHasAnnotations equation then
            pure (← Ix.Compile.SourceContract.fromAnnotations equation).binders
          else pure #[]
        let binders := existing ++ header.binders.filter fun b => !existing.any (·.site == b.site)
        Ix.Compile.registerSourceContract env { source := equation, binders }
      match registered with
      | .ok next =>
        env := next
        result := result.push { a with contracts := carried }
      | .error error =>
        failed := failed.push (a.definition, s!"contracts not carried: {error}")
        result := result.push a
  return (env, result, failed)

private def usesName : Ixon.Uses → String
  | .erased => "erased" | .linear => "linear" | .affine => "affine" | .many => "many"

/-- The sidecar's format identifier. The keys `resourceChecked` and
`resourceProfile` are optional, so a reader of the association records alone
is unaffected by them. -/
def sidecarFormat : String := "ix/compile-equations/1"

/-- What a compile under resource admission records in the sidecar: the
closure's canonical root, the effective profile when resource admission ran
(`(address, canonical bytes)`, both hex; `none` when the closure had no
resource obligation), and the pairs through which admission checked a
definition, as `(definition, equation, definition address, equation
address)`. -/
structure ResourceRecord where
  root : String
  profile : Option (String × String) := none
  checked : Array (String × String × String × String) := #[]
  deriving Inhabited, Repr

private def contractJson (c : CarriedContract) : Lean.Json := Lean.Json.mkObj [
  ("position", Lean.toJson c.position), ("binder", Lean.Json.str c.binder.toString),
  ("uses", Lean.Json.str (usesName c.uses)),
  ("owned", Lean.Json.str (if c.value.owned == .unique then "unique" else "shared")),
  ("locality", Lean.Json.str (if c.value.locality == .local then "local" else "unrestricted"))]

/-- The association records as JSON, sorted by definition name. With
`resource` (a compile under resource admission), also `"root"`, the
effective `"resourceProfile"` and, under `"resourceChecked"`, the pairs
through which resource admission checked a definition, each with both
addresses, the profile address and the contracts its equation carries: a
consumer must run each of these definitions by the bound equation's
right-hand side, fetched by address (`ix check-equations` re-verifies the
list against the closure). -/
def toJson (found : Array Association) (failed : Array (Lean.Name × String))
    (resource : Option ResourceRecord := none) : Lean.Json :=
  let found := found.qsort (fun a b => a.definition.toString < b.definition.toString)
  let checkedJson (r : ResourceRecord) := Lean.Json.arr <| r.checked.map
    fun (definition, equation, definitionAddress, equationAddress) =>
      let contracts := (found.find? (·.definition.toString == definition)).map (·.contracts) |>.getD #[]
      Lean.Json.mkObj <| [
        ("definition", Lean.Json.str definition), ("equation", Lean.Json.str equation),
        ("definitionAddress", Lean.Json.str definitionAddress),
        ("equationAddress", Lean.Json.str equationAddress)] ++
        (match r.profile with
          | some (address, _) => [("profile", Lean.Json.str address)]
          | none => []) ++
        [("contracts", Lean.Json.arr (contracts.map contractJson))]
  Lean.Json.mkObj <| [
    ("format", Lean.Json.str sidecarFormat),
    ("equations", Lean.Json.arr <| found.map fun a => Lean.Json.mkObj <| [
      ("definition", Lean.Json.str a.definition.toString),
      ("equation", Lean.Json.str a.equation.toString)] ++
      (if a.contracts.isEmpty then [] else [("contracts", Lean.Json.arr (a.contracts.map contractJson))])),
    ("failures", Lean.Json.arr <| failed.map fun (name, message) => Lean.Json.mkObj [
      ("definition", Lean.Json.str name.toString), ("message", Lean.Json.str message)])] ++
    (match resource with
    | none => []
    | some r =>
      [("root", Lean.Json.str r.root)] ++
      (match r.profile with
        | some (address, bytes) =>
          [("resourceProfile", Lean.Json.mkObj [
            ("address", Lean.Json.str address), ("bytes", Lean.Json.str bytes)])]
        | none => []) ++
      [("resourceChecked", checkedJson r)])

end Ix.Compile.Equations
