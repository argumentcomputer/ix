/-
  `Ix.Catalog`: qualified multi-library union environments ("catalogs").

  A catalog is one merged kernel `Environment` in which every constant
  `N` owned by member library `X` appears as `<prefix>.<X>.N` (lossless:
  no leading component is stripped), so libraries with colliding source
  names — two packages both declaring `Collision.Tree` — coexist in one
  environment and one `.ixe`. See `plans/upstream-from-truthmines.md`
  §3; the relocation core is absorbed from TruthMinesLib
  (`TruthMines/Internal/Relocate.lean`), reduced to the kernel level.

  Contract and deliberate simplifications:
  - **Kernel-level only.** Constants are relocated and kernel-replayed;
    instances, attributes, LCNF, and native code do not transfer.
  - **Complete bodies, unconditionally.** Libraries load at
    `OLeanLevel.private` (importModules' default), so `@[no_expose]` /
    module-sealed definitions enter the catalog as ordinary transparent
    definitions — Ix punches through the Lean module system (plan D6).
  - **Ownership is Lake package identity.** A constant is owned by the
    package of its source module (`Environment.getModulePackageByIdx?`);
    toolchain modules (no package identity) form the shared unqualified
    base. Every non-toolchain package in any member's import closure
    must be cataloged — fail closed otherwise.
  - **Kernel replay regenerates auxiliaries.** Constructors and
    recursors (including nested-aux `rec_N`) are skipped and reappear
    when the kernel re-accepts the renamed `inductDecl`; their renamed
    names coincide with the renamed references because the lossless rule
    prefixes every owned name uniformly.

  Note on qualification: bare `Expr`/`Name`/`ConstantInfo` inside the
  `Ix` namespace resolve to ix's own mirror types, so Lean's are
  `Lean.`-qualified explicitly throughout (repo convention).
-/
module

public import Lean
public import Ix.Meta
public import Ix.CanonM
public import Ix.CompileM

public section

namespace Ix.Catalog

/-- One member library: a single-component qualifier and the root
    modules whose import closure delivers the library. Libraries must be
    listed in dependency order (dependencies first). -/
structure LibSpec where
  qualifier : Lean.Name
  roots : Array Lean.Name
  deriving Repr, Inhabited

structure CatalogSpec where
  /-- The catalog's own namespace, e.g. `TruthMines`. -/
  catalogPrefix : Lean.Name
  /-- Member libraries, dependencies first. -/
  libs : Array LibSpec
  deriving Repr, Inhabited

structure BuildResult where
  /-- Every constant of the catalog environment: the unqualified
      toolchain base plus all qualified member constants (including
      kernel-regenerated constructors/recursors). -/
  consts : Array (Lean.Name × Lean.ConstantInfo)
  /-- Declarations replayed through the kernel. -/
  replayed : Nat
  /-- Per-qualifier owned-constant counts (source constants, pre-replay). -/
  perLib : Array (Lean.Name × Nat)

/-! ## Relocation core (absorbed from TruthMines `Internal.Relocate`) -/

def rename (names : Lean.NameMap Lean.Name) (name : Lean.Name) : Lean.Name :=
  names.find? name |>.getD name

/-- Rewrite both ordinary constants and the structure name embedded in
    `Expr.proj` — `getUsedConstantsAsSet` deliberately skips the latter,
    but relocation must not: changing a projected value's type without
    its type tag creates an invalid kernel projection. `Expr.replace` is
    pointer-cached, which matters for highly shared proof-term DAGs. -/
partial def relocateExpr (names : Lean.NameMap Lean.Name) (expr : Lean.Expr) :
    Lean.Expr :=
  expr.replace fun
    | .const name levels =>
      names.find? name |>.map fun name' => .const name' levels
    | .proj typeName idx value =>
      names.find? typeName |>.map fun typeName' =>
        .proj typeName' idx (relocateExpr names value)
    | _ => none

private unsafe structure ExpressionReferenceState where
  visited : Lean.PtrSet Lean.Expr := Lean.mkPtrSet
  references : Lean.NameSet := {}

private unsafe abbrev ExpressionReferenceM := StateM ExpressionReferenceState

private unsafe def expressionReferencesUnsafe (expr : Lean.Expr) :
    Lean.NameSet :=
  let rec visit (expr : Lean.Expr) : ExpressionReferenceM Unit := do
    if (← get).visited.contains expr then return
    modify fun state => { state with visited := state.visited.insert expr }
    match expr with
    | .forallE _ domain body _ | .lam _ domain body _ =>
      visit domain
      visit body
    | .mdata _ body => visit body
    | .letE _ type value body _ =>
      visit type
      visit value
      visit body
    | .app fn arg =>
      visit fn
      visit arg
    | .proj typeName _ value =>
      modify fun state => {
        state with references := state.references.insert typeName }
      visit value
    | .const name _ =>
      modify fun state => {
        state with references := state.references.insert name }
    | _ => pure ()
  (do
    visit expr
    return (← get).references : ExpressionReferenceM Lean.NameSet).run' {}

@[implemented_by expressionReferencesUnsafe]
private opaque expressionReferencesImpl (_expr : Lean.Expr) : Lean.NameSet :=
  {}

/-- All constant references of an expression, including `Expr.proj`
    structure names, with pointer-cached DAG traversal. -/
def expressionReferences (expr : Lean.Expr) : Lean.NameSet :=
  expressionReferencesImpl expr

def constantInfoReferences (info : Lean.ConstantInfo) : Lean.NameSet :=
  let result := expressionReferences info.type
  match info.value? (allowOpaque := true) with
  | some value => expressionReferences value ++ result
  | none => match info with
    | .inductInfo val => result ++ Lean.NameSet.ofList val.ctors
    | .ctorInfo val => result.insert val.name
    | .recInfo val => result ++ Lean.NameSet.ofList val.all
    | _ => result

def relocateDefinitionVal (names : Lean.NameMap Lean.Name)
    (val : Lean.DefinitionVal) : Lean.DefinitionVal :=
  { val with
    name := rename names val.name
    type := relocateExpr names val.type
    value := relocateExpr names val.value
    all := val.all.map (rename names) }

def relocateDeclaration (names : Lean.NameMap Lean.Name) :
    Lean.Declaration → Lean.Declaration
  | .axiomDecl val => .axiomDecl {
      val with
      name := rename names val.name
      type := relocateExpr names val.type }
  | .defnDecl val => .defnDecl (relocateDefinitionVal names val)
  | .thmDecl val => .thmDecl {
      val with
      name := rename names val.name
      type := relocateExpr names val.type
      value := relocateExpr names val.value
      all := val.all.map (rename names) }
  | .opaqueDecl val => .opaqueDecl {
      val with
      name := rename names val.name
      type := relocateExpr names val.type
      value := relocateExpr names val.value
      all := val.all.map (rename names) }
  | .mutualDefnDecl vals =>
      .mutualDefnDecl (vals.map (relocateDefinitionVal names))
  | .inductDecl levelParams numParams types isUnsafe =>
      .inductDecl levelParams numParams (types.map fun type => {
        name := rename names type.name
        type := relocateExpr names type.type
        ctors := type.ctors.map fun ctor => {
          name := rename names ctor.name
          type := relocateExpr names ctor.type } }) isUnsafe
  | .quotDecl => .quotDecl

def relocateConstantVal (names : Lean.NameMap Lean.Name)
    (cv : Lean.ConstantVal) : Lean.ConstantVal :=
  { cv with
    name := rename names cv.name
    type := relocateExpr names cv.type }

/-- Rewrite a `ConstantInfo` in place under a rename map — every name
    field (self, `all` lists, inductive families, recursor rules) and
    every expression. Compile-layer relocation: use when comparing
    qualified against unqualified compiles without kernel replay (the
    C5 anon-invariance gate); `buildCatalog` itself replays
    `Declaration`s instead. -/
def relocateConstantInfo (names : Lean.NameMap Lean.Name) :
    Lean.ConstantInfo → Lean.ConstantInfo
  | .axiomInfo v => .axiomInfo {
      v with toConstantVal := relocateConstantVal names v.toConstantVal }
  | .defnInfo v => .defnInfo {
      v with
      toConstantVal := relocateConstantVal names v.toConstantVal
      value := relocateExpr names v.value
      all := v.all.map (rename names) }
  | .thmInfo v => .thmInfo {
      v with
      toConstantVal := relocateConstantVal names v.toConstantVal
      value := relocateExpr names v.value
      all := v.all.map (rename names) }
  | .opaqueInfo v => .opaqueInfo {
      v with
      toConstantVal := relocateConstantVal names v.toConstantVal
      value := relocateExpr names v.value
      all := v.all.map (rename names) }
  | .quotInfo v => .quotInfo {
      v with toConstantVal := relocateConstantVal names v.toConstantVal }
  | .inductInfo v => .inductInfo {
      v with
      toConstantVal := relocateConstantVal names v.toConstantVal
      all := v.all.map (rename names)
      ctors := v.ctors.map (rename names) }
  | .ctorInfo v => .ctorInfo {
      v with
      toConstantVal := relocateConstantVal names v.toConstantVal
      induct := rename names v.induct }
  | .recInfo v => .recInfo {
      v with
      toConstantVal := relocateConstantVal names v.toConstantVal
      all := v.all.map (rename names)
      rules := v.rules.map fun rule => {
        rule with
        ctor := rename names rule.ctor
        rhs := relocateExpr names rule.rhs } }

/-- Accept a `DefinitionVal.all` list as unsafe-mutual grouping metadata
    only when every member is an owned definition carrying the same
    list — code-generating metaprograms may copy a recursor's `all` into
    an unrelated definition. -/
def definitionWorkGroup (owned : Lean.NameMap Lean.ConstantInfo)
    (name : Lean.Name) (val : Lean.DefinitionVal) : List Lean.Name :=
  Id.run do
    if val.safety == .safe || !val.all.contains name then
      return [name]
    for member in val.all do
      match owned.find? member with
      | some (.defnInfo memberVal) =>
        unless memberVal.safety == val.safety && memberVal.all == val.all do
          return [name]
      | _ => return [name]
    return val.all

/-- The replay-work key that produces `name`: inductive blocks key on
    `all.head`, constructors and recursors on their block's key, unsafe
    mutual definitions on the group head; everything else is its own
    item. -/
def canonicalWorkKey (owned : Lean.NameMap Lean.ConstantInfo)
    (name : Lean.Name) : Lean.Name :=
  match owned.find? name with
  | some (.inductInfo val) => val.all.head?.getD name
  | some (.ctorInfo val) =>
      match owned.find? val.induct with
      | some (.inductInfo inductiveVal) =>
          inductiveVal.all.head?.getD val.induct
      | _ => val.induct
  | some (.recInfo val) => val.all.head?.getD name
  | some (.defnInfo val) => (definitionWorkGroup owned name val).head?.getD name
  | _ => name

private def sourceInductiveDeclaration
    (find? : Lean.Name → Option Lean.ConstantInfo)
    (owned : Lean.NameMap Lean.ConstantInfo) (val : Lean.InductiveVal) :
    Except String Lean.Declaration := do
  let mut types : List Lean.InductiveType := []
  for typeName in val.all do
    let some (.inductInfo typeVal) := owned.find? typeName
      | throw s!"missing inductive `{typeName}` from mutual block rooted at `{val.name}`"
    let mut ctors : List Lean.Constructor := []
    for ctorName in typeVal.ctors do
      let some (.ctorInfo ctorVal) := find? ctorName
        | throw s!"missing constructor `{ctorName}` for inductive `{typeName}`"
      ctors := ctors.concat { name := ctorName, type := ctorVal.type }
    types := types.concat { name := typeName, type := typeVal.type, ctors }
  return .inductDecl val.levelParams val.numParams types val.isUnsafe

/-- The `Declaration` that replays `info`, or `none` when the constant
    is produced by another work item (constructors, recursors, non-head
    inductive/mutual members) or by the base env (`Quot`). `find?`
    resolves constructor lookups (callers back it by the source
    environment or the materialized constant map). -/
private def sourceDeclaration?
    (find? : Lean.Name → Option Lean.ConstantInfo)
    (owned : Lean.NameMap Lean.ConstantInfo) (name : Lean.Name)
    (info : Lean.ConstantInfo) : Except String (Option Lean.Declaration) := do
  match info with
  | .axiomInfo val => return some (.axiomDecl val)
  | .defnInfo val =>
      if val.safety != .safe then
        let group := definitionWorkGroup owned name val
        if group.head? != some name then return none
        let mut vals : List Lean.DefinitionVal := []
        for defName in group do
          let some (.defnInfo defVal) := owned.find? defName
            | throw s!"missing definition `{defName}` from mutual block rooted at `{name}`"
          vals := vals.concat defVal
        return some (.mutualDefnDecl vals)
      else
        return some (.defnDecl val)
  | .thmInfo val => return some (.thmDecl val)
  | .opaqueInfo val => return some (.opaqueDecl val)
  | .inductInfo val =>
      if val.all.head? == some name then
        return some (← sourceInductiveDeclaration find? owned val)
      else
        return none
  | .ctorInfo _ | .recInfo _ | .quotInfo _ => return none

/-! ## Kernel replay driver -/

private def renderKernelException : Lean.Kernel.Exception → String
  | .unknownConstant _ n => s!"unknown constant `{n}`"
  | .alreadyDeclared _ n => s!"`{n}` already declared"
  | .declTypeMismatch _ _ _ => "declaration type mismatch"
  | .declHasMVars _ n _ => s!"`{n}` has metavariables"
  | .declHasFVars _ n _ => s!"`{n}` has free variables"
  | .funExpected _ _ _ => "function expected"
  | .typeExpected _ _ _ => "type expected"
  | .letTypeMismatch _ _ n _ _ => s!"let type mismatch at `{n}`"
  | .exprTypeMismatch _ _ _ _ => "expression type mismatch"
  | .appTypeMismatch _ _ _ _ _ => "application type mismatch"
  | .invalidProj _ _ _ => "invalid projection"
  | .thmTypeIsNotProp _ n _ => s!"theorem type of `{n}` is not a Prop"
  | .other msg => msg
  | .deterministicTimeout => "deterministic timeout"
  | .excessiveMemory => "excessive memory"
  | .deepRecursion => "deep recursion"
  | .interrupted => "interrupted"

/-- The package that owns module `moduleIdx`, `none` for toolchain. -/
private def modulePackage? (env : Lean.Environment) (moduleIdx : Nat) :
    Option Lean.PkgId :=
  env.getModulePackageByIdx? moduleIdx

/-- The constants serialized by module `moduleIdx`, resolved through the
    environment so private-part key remapping matches ordinary lookup. -/
private def moduleConstants (env : Lean.Environment) (moduleIdx : Nat) :
    Except String (Array (Lean.Name × Lean.ConstantInfo)) := do
  let some data := env.header.moduleData[moduleIdx]?
    | throw s!"module index {moduleIdx} has no serialized module data"
  let mut result := Array.mkEmpty data.constNames.size
  for name in data.constNames do
    let some info := env.find? name
      | throw s!"module `{env.header.moduleNames[moduleIdx]!}` does not expose serialized declaration `{name}`"
    result := result.push (name, info)
  return result

private structure WorkItem where
  key : Lean.Name
  decl : Lean.Declaration
  deps : Lean.NameSet

/-- Reconstruct the kernel `Declaration`s that replay `owned` and order
    them topologically (Kahn's algorithm, name-sorted ready sets for
    determinism). Pure planning — no kernel interaction; dependencies
    outside `owned` are assumed satisfied by the caller's base
    environment. `find?` resolves constructor lookups during inductive
    reconstruction. Shared by the catalog replay driver and by
    `import_ixe` materialization (`Ix/ImportIxe.lean`). -/
def planDeclarations (owned : Lean.NameMap Lean.ConstantInfo)
    (find? : Lean.Name → Option Lean.ConstantInfo) :
    Except String (Array (Lean.Name × Lean.Declaration)) := do
  -- Work items keyed by canonical head, with owned-only dependencies.
  let mut producedBy : Lean.NameMap Lean.Name := {}
  let mut membersOfKey : Lean.NameMap (Array Lean.Name) := {}
  for (name, _) in owned do
    let key := canonicalWorkKey owned name
    producedBy := producedBy.insert name key
    membersOfKey := membersOfKey.insert key
      ((membersOfKey.find? key).getD #[] |>.push name)
  let mut items : Lean.NameMap WorkItem := {}
  for (name, info) in owned do
    let some decl ← sourceDeclaration? find? owned name info | continue
    let key := name
    -- Dependencies: references of every constant this item produces,
    -- mapped to their producing items.
    let mut deps : Lean.NameSet := {}
    for member in (membersOfKey.find? key).getD #[] do
      let some memberInfo := owned.find? member | continue
      for reference in constantInfoReferences memberInfo do
        match producedBy.find? reference with
        | some refKey => if refKey != key then deps := deps.insert refKey
        | none => pure ()
    items := items.insert key { key, decl, deps }
  -- Kahn's algorithm with name-sorted ready set for determinism.
  let mut plan : Array (Lean.Name × Lean.Declaration) := #[]
  let mut added : Lean.NameSet := {}
  let mut pending := items
  while !pending.isEmpty do
    let mut ready : Array WorkItem := #[]
    for (_, item) in pending do
      if item.deps.all (added.contains ·) then
        ready := ready.push item
    if ready.isEmpty then
      let cycle := pending.foldl (init := #[]) fun acc k _ => acc.push k
      throw s!"dependency cycle among replay items: {cycle[0:8].toArray}"
    let readySorted := ready.qsort fun a b => a.key.quickCmp b.key == .lt
    for item in readySorted do
      plan := plan.push (item.key, item.decl)
      added := added.insert item.key
      pending := pending.erase item.key
  return plan

/-- Per-module ownership sweep over one loaded library environment:
    rename entries for every cataloged package's constants, plus the
    owned map for this library's own packages. Fails closed on
    uncatalogued packages. Shared by the replay driver and the audit. -/
private def ownershipMaps (spec : CatalogSpec) (env : Lean.Environment)
    (qualOfPkg : Std.HashMap Lean.PkgId Lean.Name)
    (libPkgs : Std.HashSet Lean.PkgId) :
    Except String
      (Lean.NameMap Lean.Name × Lean.NameMap Lean.ConstantInfo) := do
  let mut renameMap : Lean.NameMap Lean.Name := {}
  let mut owned : Lean.NameMap Lean.ConstantInfo := {}
  for moduleIdx in [0:env.header.moduleNames.size] do
    match modulePackage? env moduleIdx with
    | none => pure ()  -- toolchain base: unqualified, provided by baseEnv
    | some pkg =>
      let some qualifier := qualOfPkg.get? pkg
        | throw s!"uncatalogued package `{pkg}` (module `{env.header.moduleNames[moduleIdx]!}`) — every non-toolchain package in the import closure needs a catalog entry"
      let target := spec.catalogPrefix ++ qualifier
      for (name, info) in ← moduleConstants env moduleIdx do
        renameMap := renameMap.insert name (target ++ name)
        if libPkgs.contains pkg then
          owned := owned.insert name info
  return (renameMap, owned)

/-- Replay one library's owned constants into the growing kernel env:
    build the per-env rename map, reconstruct declarations, order by
    owned-reference dependencies, and `Kernel.Environment.addDecl` each
    relocated declaration. Returns the updated env, the replay count,
    and the owned source-constant count. -/
private def replayLib (spec : CatalogSpec) (env : Lean.Environment)
    (qualOfPkg : Std.HashMap Lean.PkgId Lean.Name)
    (libPkgs : Std.HashSet Lean.PkgId) (kenv : Lean.Kernel.Environment) :
    Except String (Lean.Kernel.Environment × Nat × Nat) := do
  let (renameMap, owned) ← ownershipMaps spec env qualOfPkg libPkgs
  let plan ← planDeclarations owned env.find?
  let mut kenv := kenv
  let mut replayed := 0
  for (key, decl) in plan do
    let relocated := relocateDeclaration renameMap decl
    match kenv.addDecl {} relocated with
    | .ok kenv' =>
      kenv := kenv'
      replayed := replayed + 1
    | .error e =>
      throw s!"kernel rejected `{rename renameMap key}` (source `{key}`): {renderKernelException e}"
  return (kenv, replayed, owned.size)

/-- Load every member library into its own environment (complete
    bodies: `OLeanLevel.private` is the importModules default — so
    colliding source names never meet at import time) and resolve the
    package → qualifier map from each library's root modules. Shared by
    `buildCatalog` and `auditCatalog`. -/
def resolveLibs (spec : CatalogSpec) :
    IO (Array Lean.Environment × Std.HashMap Lean.PkgId Lean.Name ×
        Array (Std.HashSet Lean.PkgId)) := do
  if spec.libs.isEmpty then
    throw <| IO.userError "catalog: no member libraries"
  let mut libEnvs : Array Lean.Environment := #[]
  for lib in spec.libs do
    let imports : Array Lean.Import := lib.roots.map ({ module := · })
    libEnvs := libEnvs.push (← Lean.importModules imports {})
  let mut qualOfPkg : Std.HashMap Lean.PkgId Lean.Name := {}
  let mut libPkgs : Array (Std.HashSet Lean.PkgId) := #[]
  for (lib, env) in spec.libs.zip libEnvs do
    let mut pkgs : Std.HashSet Lean.PkgId := {}
    for root in lib.roots do
      let some moduleIdx := env.getModuleIdx? root
        | throw <| IO.userError s!"catalog: root module `{root}` is not in `{lib.qualifier}`'s environment"
      let some pkg := modulePackage? env moduleIdx.toNat
        | throw <| IO.userError s!"catalog: root module `{root}` has no Lake package identity — toolchain modules cannot be cataloged"
      pkgs := pkgs.insert pkg
      match qualOfPkg.get? pkg with
      | some q =>
        unless q == lib.qualifier do
          throw <| IO.userError s!"catalog: package `{pkg}` claimed by qualifiers `{q}` and `{lib.qualifier}`"
      | none => qualOfPkg := qualOfPkg.insert pkg lib.qualifier
    libPkgs := libPkgs.push pkgs
  return (libEnvs, qualOfPkg, libPkgs)

/-- Build the catalog kernel environment for `spec`. Assumes the Lean
    search path already resolves every root module (CLI callers run
    `initLeanSearchPath` first; in-process callers inherit theirs). -/
def buildCatalog (spec : CatalogSpec) : IO BuildResult := do
  -- 1./2. Load member envs and resolve package ownership.
  let (libEnvs, qualOfPkg, libPkgs) ← resolveLibs spec
  -- 3. Toolchain base: the union of toolchain modules across member
  --    environments, imported once (single provider ⇒ no collisions).
  let mut toolchainSeen : Lean.NameSet := {}
  let mut toolchainMods : Array Lean.Import := #[]
  for env in libEnvs do
    for moduleIdx in [0:env.header.moduleNames.size] do
      let moduleName := env.header.moduleNames[moduleIdx]!
      if (modulePackage? env moduleIdx).isNone
          && !toolchainSeen.contains moduleName then
        toolchainSeen := toolchainSeen.insert moduleName
        toolchainMods := toolchainMods.push { module := moduleName }
  let baseEnv ← Lean.importModules toolchainMods {}
  -- 4. Relocate + kernel-replay each library in dependency order.
  let mut kenv := baseEnv.toKernelEnv
  let mut replayed := 0
  let mut perLib : Array (Lean.Name × Nat) := #[]
  for (lib, env, pkgs) in spec.libs.zip (libEnvs.zip libPkgs) do
    match replayLib spec env qualOfPkg pkgs kenv with
    | .ok (kenv', count, ownedCount) =>
      kenv := kenv'
      replayed := replayed + count
      perLib := perLib.push (lib.qualifier, ownedCount)
    | .error e =>
      throw <| IO.userError s!"catalog: library `{lib.qualifier}`: {e}"
  -- 5. Extract the full constant map (base + qualified + regenerated).
  let consts := kenv.constants.fold (init := #[]) fun acc name info =>
    acc.push (name, info)
  return { consts, replayed, perLib }

/-! ## Audit: anon-address preservation (the §3.1 invariant) -/

structure AuditResult where
  /-- Owned constants whose addresses were compared. -/
  checked : Nat
  /-- Human-readable invariant violations; empty = pass. -/
  violations : Array String

/-- Audit a built catalog against the load-bearing §3.1 invariant:
    qualification is metadata-only at the Ixon layer, so for every
    owned constant `N` of member `X`, the anon address of the
    standalone library compile at `N` equals the catalog compile's at
    `P.X.N`. Each member library is recompiled standalone (its own env,
    unqualified) and compared against one compile of the catalog —
    N+1 Rust compiles, so this is an opt-in gate (`ix catalog --audit`),
    not part of the build. -/
def auditCatalog (spec : CatalogSpec)
    (catalogConsts : Array (Lean.Name × Lean.ConstantInfo)) :
    IO AuditResult := do
  let (libEnvs, qualOfPkg, libPkgs) ← resolveLibs spec
  let catEnv ← Ix.CompileM.rsCompileEnvOf catalogConsts.toList
  let mut violations : Array String := #[]
  let mut checked := 0
  for (lib, env, pkgs) in spec.libs.zip (libEnvs.zip libPkgs) do
    let (renameMap, owned) ←
      match ownershipMaps spec env qualOfPkg pkgs with
      | .ok maps => pure maps
      | .error e =>
        throw <| IO.userError s!"catalog audit: `{lib.qualifier}`: {e}"
    let stdEnv ← Ix.CompileM.rsCompileEnvOf env.constants.toList
    for (name, _) in owned do
      let target := rename renameMap name
      let (ixSrc, _) := (CanonM.canonName name).run {}
      let (ixTgt, _) := (CanonM.canonName target).run {}
      match stdEnv.named.get? ixSrc, catEnv.named.get? ixTgt with
      | some src, some tgt =>
        checked := checked + 1
        if src.addr != tgt.addr then
          violations := violations.push
            s!"{lib.qualifier}: addr({name}) = {src.addr} standalone \
but addr({target}) = {tgt.addr} in the catalog"
      | none, _ =>
        violations := violations.push
          s!"{lib.qualifier}: standalone compile has no named entry \
for `{name}`"
      | _, none =>
        violations := violations.push
          s!"{lib.qualifier}: catalog compile has no named entry for \
`{target}`"
  return { checked, violations }

end Ix.Catalog
