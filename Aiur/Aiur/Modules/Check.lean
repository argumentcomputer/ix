import Aiur.Modules.Opacity

namespace Aiur.Modules

def stub (f : Callable) : Generic.Function α := {
  name := f.name, typeParams := f.typeParams, params := f.params, result := f.result
  body := .call f.name (some (f.typeParams.map Generic.Ty.param)) (f.params.map fun p => .var p.1) }

/-- Ordinary abstract members promise input admissibility. Opaque members
withhold it. Private constructors occur only in the checking environment. -/
def interfaceProgram (s : Signature) (aliasTarget : Option String := none) : Generic.Program α := {
  functions := s.functions.map stub
  enums := s.types.filterMap fun t =>
    if t.definition.isSome || aliasTarget.isSome then none
    else some ⟨t.name, t.typeParams, [⟨"@abstract",
      if t.isOpaque then [.ptr .field] else t.typeParams.map .param⟩]⟩
  aliases := s.types.filterMap fun t =>
    match t.definition with
    | some type => some ⟨t.name, t.typeParams, type⟩
    | none => aliasTarget.map fun target =>
        ⟨t.name, t.typeParams, .named (rename target ((splitPath t.name).getLast!)) (t.typeParams.map .param)⟩
  tables := s.tables.map fun (n,t) => ⟨n,t,[]⟩ }

def headers (p : Generic.Program α) : Generic.Program α := {
  p with
  functions := p.functions.map (fun f => stub ⟨f.name,f.typeParams,f.params,f.result⟩) ++
    p.maps.map (fun f => stub ⟨f.name,[],f.params,f.result⟩)
  maps := [], consts := [], tables := p.tables.map fun t => {t with rows := []} }

def publicView (p : Program α) (w : World α) :
    Nat → Item α → List (String × Generic.Ty) → Except String (Generic.Program α × List (String × Generic.Ty))
  | 0, _, _ => throw "interface alias depth exceeded"
  | fuel + 1, item, constants => do
      if let some sig := item.decl.signature then
        let some signature := p.findSignature? sig | throw s!"unknown signature '{sig}'"
        let (signature, _) ← (qualifySignature p item signature).run w
        return (interfaceProgram signature (item.target.map Ref.symbol), signature.consts)
      else if let some target := item.target then
        let some targetItem := w.find? target | throw "missing alias interface"
        let (base, consts) ← publicView p w fuel targetItem constants
        let renamed := fun n => rename item.key.symbol ((splitPath n).getLast!)
        let types := base.nominals.map (fun t => (t.name,t.typeParams)) ++ base.aliases.map (fun t => (t.name,t.typeParams))
        let aliases := types.map fun (n,ps) => Generic.AliasDecl.mk (renamed n) ps (.named n (ps.map .param))
        let functions := base.functions.map fun f => stub ⟨renamed f.name, f.typeParams, f.params, f.result⟩
        let tables := base.tables.map fun t => {t with name := renamed t.name}
        let templates := base.consts.map fun c => Generic.ConstDecl.mk (renamed c.name) (.global c.name)
        return ({ functions, aliases, tables, consts := templates }, consts.map fun (n,t) => (renamed n,t))
      else
        let raw := item.qualified.getD {functions := []}
        -- An inferred interface exposes const templates as well as their
        -- inferred types. Context-dependent constructors remain polymorphic;
        -- references into sealed modules still use those modules' interfaces.
        return (sealTypes {headers raw with consts := raw.consts} item.declaredOpaqueTypes,
          constants.filter fun (n,_) => raw.consts.any (·.name == n))

def rawModuleView (p : Program α) (w : World α) (owner : Ref)
    (constants : List (String × Generic.Ty)) : Except String (Generic.Program α × List (String × Generic.Ty)) := do
  let mut result : Generic.Program α := { functions := [] }
  let mut external := []
  for item in w.items do
    if item.key == owner && item.target.isNone then
      result := append result (item.qualified.getD {functions := []})
    else
      let (view, consts) ← publicView p w 128 item constants
      result := append result view
      external := external ++ consts
  return (result, external)

def normalizeView (result : Generic.Program α) (external : List (String × Generic.Ty)) :
    Except String (Generic.Program α × List (String × Generic.Ty)) := do
  let aliases ← Generic.Aliases.resolveDeclarations result
  let expanded ← Generic.Aliases.expandProgram aliases result
  let externalTypes ← external.mapM fun (n,t) => return (n, ← Generic.Aliases.expandType aliases t)
  return ({expanded with aliases},externalTypes)

def moduleView (p : Program α) (w : World α) (owner : Ref)
    (constants : List (String × Generic.Ty)) : Except String (Generic.Program α × List (String × Generic.Ty)) := do
  let (raw, external) ← rawModuleView p w owner constants
  normalizeView raw external

def normalized (view : Generic.Program α) (t : Generic.Ty) := do
  Generic.Aliases.expandType (← Generic.Aliases.resolveDeclarations view) t

def inferConstants (p : Program α) (w : World α) : Except String (List (String × Generic.Ty)) := do
  let mut constants := []
  let mut failure := "cannot infer exported constant types"
  let total := (w.items.map fun i => (i.qualified.getD {functions := []}).consts.length).sum
  for _ in List.range (total + 1) do
    let mut next := constants
    for item in w.items do
      if item.target.isSome || item.key.name.startsWith "@" then continue
      match moduleView p w item.key constants with
      | .error e => failure := e
      | .ok (view, external) =>
          for c in (item.qualified.getD {functions := []}).consts do
            let checked : Except String Generic.Ty := do
              let some body := view.consts.find? (·.name == c.name) | throw "missing constant"
              let annotation ← (item.constTypes.lookup c.name).mapM (normalized view)
              Generic.inferInterfaceConst view body.value annotation external false
            match checked with
            | .ok type => if type.concrete then
                let exposed := (item.constTypes.lookup c.name).getD type
                next := (c.name,exposed) :: next.filter (·.1 != c.name)
            | .error e => failure := s!"in const '{c.name}': {e}"
    if next == constants then break
    constants := next
  for item in w.items do
    if item.target.isSome || item.key.name.startsWith "@" then continue
    let (view, external) ← moduleView p w item.key constants
    for c in (item.qualified.getD {functions := []}).consts do
      if (constants.lookup c.name).isNone then
        let some body := view.consts.find? (·.name == c.name) | throw failure
        let annotation ← (item.constTypes.lookup c.name).mapM (normalized view)
        let _ ← (Generic.inferInterfaceConst view body.value annotation external false).mapError
          (fun e => s!"in const '{c.name}': {e}")
  return constants

def checkContract (p : Program α) (w : World α) (constants : List (String × Generic.Ty))
    (item : Item α) (signature : String) (throughInterface : Bool) : Except String Unit := do
  let some sig := p.findSignature? signature | throw s!"unknown signature '{signature}'"
  let (required, _) ← (qualifySignature p item sig).run w
  let owner := if throughInterface || item.target.isSome then Ref.mk "" [] else item.key
  let (raw, external) ← rawModuleView p w owner constants
  -- Conformance must preserve opaque identity in every exposed signature.
  let (view, external) ← normalizeView (sealTypes raw item.declaredOpaqueTypes) external
  let available ← if throughInterface || item.target.isSome then (publicView p w 128 item constants).map Prod.fst
    else pure (item.qualified.getD {functions := []})
  for t in required.types do
    let arity := (available.nominals.find? (·.name == t.name)).map (·.typeParams.length) |>.orElse fun _ =>
      (available.aliases.find? (·.name == t.name)).map (·.typeParams.length)
    if arity != some t.typeParams.length then throw s!"missing or incompatible type '{t.name}' required by '{signature}'"
    unless t.isOpaque do
      checkNonOpaque raw (opaqueNames p w owner)
        s!"non-opaque signature member '{t.name}'" (.named t.name (t.typeParams.map .param)) t.typeParams
    if let some expected := t.definition then
      let actual ← normalized view (.named t.name (t.typeParams.map .param))
      let expected ← normalized view expected
      if actual != expected then throw s!"manifest type mismatch for '{t.name}' in signature '{signature}'"
  for f in required.functions do
    let arity := (available.functions.find? (·.name == f.name)).map (·.typeParams.length) |>.orElse fun _ =>
      (available.maps.find? (·.name == f.name)).map (fun _ => 0)
    if arity != some f.typeParams.length then throw s!"missing or incompatible callable '{f.name}' required by '{signature}'"
    let params ← f.params.mapM fun (n,t) => return (n, ← normalized view t)
    let result ← normalized view f.result
    let _ ← Generic.elaborateExpr view f.typeParams params
      (.call f.name (some (f.typeParams.map .param)) (params.map fun p => .var p.1)) result false external
  for (name,type) in required.consts do
    let types := if throughInterface || item.target.isSome then external else constants
    let actual ← match types.lookup name with
      | some type => pure type
      | none => do
          let some body := view.consts.find? (·.name == name) | throw s!"missing const '{name}' required by '{signature}'"
          Generic.inferInterfaceConst view body.value (some (← normalized view type)) external
    if (← normalized view actual) != (← normalized view type) then throw s!"const type mismatch for '{name}' in signature '{signature}'"
  for (name,type) in required.tables do
    let some table := available.tables.find? (·.name == name) | throw s!"missing table '{name}' required by '{signature}'"
    if (← normalized view table.rowType) != (← normalized view type) then throw s!"table type mismatch for '{name}'"

def checkWorld (p : Program α) (w : World α) : Except String Unit := do
  -- Sealing must not hide alias cycles spanning several modules. Check the
  -- complete declaration graph as well as each client's restricted view.
  let mut declarations : Generic.Program α := {functions := []}
  for item in w.items do
    let definition ← if item.target.isNone then pure (item.qualified.getD {functions := []})
      else (publicView p w 128 item []).map Prod.fst
    declarations := append declarations definition
  let _ ← Generic.Aliases.resolveDeclarations declarations
  let constants ← inferConstants p w
  let mut dependencies : List (Generic.Function α) := []
  for item in w.items do
    let (raw, _) ← rawModuleView p w item.key constants
    let (view, external) ← moduleView p w item.key constants
    -- Validate declarations, including interfaces and unused generic data types.
    let _ ← Generic.elaborate ({ view with functions := [], consts := [], tables := [], maps := [] } : Generic.Program α)
    if !item.key.name.startsWith "@" then
      if let some sig := item.decl.signature then
        (checkContract p w constants item sig false).mapError (fun e => s!"module '{item.key.symbol}' does not satisfy '{sig}': {e}")
    if let some target := item.target then
      let (exposed,_) ← publicView p w 128 item constants
      dependencies := dependencies ++ exposed.functions.map fun fn =>
        {fn with
          -- Aliases are transparent edges, including for inline-cycle checks.
          isInline := true
          body := .call (rename target.symbol ((splitPath fn.name).getLast!))
            (some (fn.typeParams.map .param)) (fn.params.map fun p => .var p.1)}
      continue
    let own := item.qualified.getD {functions := []}
    let mut checked := []
    for fn in own.functions do
      for type in hintTypes fn.body do
        checkNonOpaque raw (opaqueNames p w item.key) s!"hint in '{fn.name}'" type
      let some fn := view.findFunction? fn.name | throw "missing function in module view"
      Generic.checkParams fn.typeParams
      if let some n := findDuplicate (fn.params.map Prod.fst) [] then throw s!"duplicate parameter '{n}'"
      (fn.params.map Prod.snd ++ [fn.result]).forM (Generic.checkType view fn.typeParams)
      let body ← (Generic.elaborateExpr view fn.typeParams fn.params fn.body fn.result true external).mapError
        (fun e => s!"in module '{item.key.symbol}', function '{fn.name}': {e}")
      checked := checked ++ [{fn with body}]
    dependencies := dependencies ++ checked
    Generic.checkGenericCycles {view with functions := checked ++ view.functions.filter (fun f => !own.functions.any (·.name == f.name))}
    for table in own.tables do
      let some table := view.tables.find? (·.name == table.name) | throw "missing table"
      Generic.checkPointerFree view s!"table '{table.name}'" 1024 [] table.rowType
      for row in table.rows do
        let _ ← Generic.elaborateExpr view [] [] row table.rowType false external
    for m in own.maps do
      let some m := view.maps.find? (·.name == m.name) | throw "missing map"
      (m.params.map Prod.snd ++ [m.result]).forM (Generic.checkPointerFree view s!"map '{m.name}'" 1024 [])
      let some input := view.tables.find? (·.name == m.input) | throw s!"unknown input table '{m.input}'"
      let some output := view.tables.find? (·.name == m.output) | throw s!"unknown output table '{m.output}'"
      if input.rowType != .tuple (m.params.map Prod.snd) || output.rowType != m.result then
        throw s!"table type mismatch for map '{m.name}'"
    for (_,patterns) in item.parameterPatterns do
      let aliases ← Generic.Aliases.resolveDeclarations view
      for pat in patterns do
        let pat ← Generic.Aliases.expandPattern aliases pat
        -- Constants are always refutable; other patterns use exposed shapes.
        if !pat.irrefutable view.nominals then throw "parameter patterns must be irrefutable"
  -- Interface-only body checking must not hide a growing generic recursion
  -- path that crosses module boundaries, including aliases and unused functors.
  Generic.checkGenericCycles {functions := dependencies}
  Generic.checkInlineCycles {functions := dependencies}
  for (key,sig) in w.requirements do
    let some item := w.find? key | throw "missing module argument"
    (checkContract p w constants item sig true).mapError (fun e => s!"module argument '{key.symbol}' does not satisfy '{sig}': {e}")

def abstractModule (name : String) (sig : Signature) : Module α := {
  name, signature := some sig.name
  body := .definitions ⟨interfaceProgram sig, [], [], (sig.types.filter (·.isOpaque)).map (·.name)⟩ }

/-- Independent abstract arguments preserve each module parameter's permissions,
even when two parameters are later instantiated with the same concrete module. -/
def templateContext (p : Program α) : Except String (Program α × List Ref) := do
  let signatureModules := p.signatures.map fun s => abstractModule ("@signature:" ++ s.name) s
  let mut extra := signatureModules
  let mut seeds := []
  for m in p.modules do
    if m.parameters.isEmpty then continue
    let mut args := []
    for (n,sig) in m.parameters do
      let some signature := p.findSignature? sig | throw s!"unknown signature '{sig}'"
      let name := "@parameter:" ++ m.name ++ ":" ++ n
      extra := extra ++ [abstractModule name signature]
      args := args ++ [.mk name []]
    seeds := seeds ++ [.mk m.name args]
  return ({p with modules := p.modules ++ extra}, seeds)

/-- Entry selection uses the externally supplied interface before alias
normalization. Internal functions may continue to accept opaque values. -/
def checkEntryInputs (p : Program α) (w : World α) (external : String) : Except String Unit := do
  let ((target, member), w) ← (locate p (.mk "" []) [] external).run w
  let constants ← inferConstants p w
  let (view, _) ← rawModuleView p w (.mk "" []) constants
  let name := rename target.symbol member
  let some fn := view.findFunction? name | throw s!"unknown entry function '{external}'"
  for (_, type) in fn.params do
    checkNonOpaque view (opaqueNames p w (.mk "" [])) s!"entry '{external}'" type
  let some item := w.find? target | throw "missing entry module"
  let some implementation := w.find? item.canonical | throw "missing entry implementation"
  unless implementation.decl.parameters.isEmpty do
    let (abstract, seeds) ← templateContext p
    let (world, _) ← collect abstract [] seeds
    let key := Ref.mk implementation.decl.name (implementation.decl.parameters.map fun (n, _) =>
      .mk ("@parameter:" ++ implementation.decl.name ++ ":" ++ n) [])
    let (view, _) ← rawModuleView abstract world key []
    let some fn := view.findFunction? (rename key.symbol member) |
      throw "missing abstract entry implementation"
    for (_, type) in fn.params do
      checkNonOpaque view (opaqueNames abstract world key)
        s!"entry '{external}' under its module signature" type

/-- Check every template once with abstract module arguments. No concrete
application can make an invalid unused template acceptable. -/
def checkTemplates (p : Program α) : Except String Unit := do
  validate p
  let (abstract, seeds) ← templateContext p
  let (world,_) ← collect abstract [] seeds
  checkWorld abstract world
  -- Validate the permission promised by manifest members in the signature
  -- itself; a particular transparent implementation must not justify it.
  for sig in p.signatures do
    let owner := Ref.mk ("@signature:" ++ sig.name) []
    let (view, _) ← rawModuleView abstract world owner []
    for type in sig.types do
      unless type.isOpaque do
        checkNonOpaque view (opaqueNames abstract world owner)
          s!"non-opaque signature member '{sig.name}::{type.name}'"
          (.named (rename owner.symbol type.name) (type.typeParams.map .param)) type.typeParams

end Aiur.Modules
