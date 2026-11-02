/-
  Ix.Frontend.Scope: Pass 1 of the Ix Frontend — Lexical Scope Management,
  First-Class `Name -> Address` Build/Import Mapping (`IxImportMap`),
  and Pre-Elaboration Module Symbol Table (`ModuleIndex`).
-/
module

public import Std.Data.TreeMap
public import Std.Data.TreeSet
public import Ix.Frontend.Parser.Command

@[expose] public section

namespace Ix.Frontend

open Ix.Frontend.Parser

/-- Canonical structural comparator on `Ix.Name` (`Name.cmpStruct`, which reads no hash)
    for `Std.TreeMap` / `Std.TreeSet`. -/
abbrev NameMap (α : Type) := Std.TreeMap Ix.Name α Name.cmpStruct
abbrev NameSet := Std.TreeSet Ix.Name Name.cmpStruct

namespace NameMap

def empty : NameMap α := Std.TreeMap.empty

end NameMap

namespace NameSet

def empty : NameSet := Std.TreeSet.empty

end NameSet

/-! ## Hex Address Decoding & First-Class `IxImportMap` -/

/-- Parse a 64-character hex string into a 32-byte `Address`. -/
def parseHexBytesAux : List Char → Array UInt8 → Option ByteArray
  | [], acc =>
    if acc.size == 32 then some ⟨acc⟩ else none
  | c1 :: c2 :: rest, acc => do
    let hi ← natOfHex c1
    let lo ← natOfHex c2
    let byte : UInt8 := UInt8.ofNat (hi * 16 + lo)
    parseHexBytesAux rest (acc.push byte)
  | _, _ => none

def parseHexAddress (hex : String) : Option Address := do
  let ba ← parseHexBytesAux hex.toList (Array.mkEmpty 32)
  return ⟨ba⟩

/-- First-class programmable `Name -> Address` mapping and content-hash import table
    extracted from `.ix` files (`map Foo.Bar := #<hash>`, `import #<hash>`, `import Mod @ #<hash>`). -/
structure IxImportMap where
  nameToAddr   : NameMap Address := NameMap.empty
  modulePins   : NameMap Address := NameMap.empty
  importedEnvs : Array Address   := #[]
  deriving Repr, Inhabited

namespace IxImportMap

def empty : IxImportMap := {}

def insertName (m : IxImportMap) (name : Ix.Name) (addr : Address) : IxImportMap :=
  { m with nameToAddr := m.nameToAddr.insert name addr }

def insertModulePin (m : IxImportMap) (modName : Ix.Name) (addr : Address) : IxImportMap :=
  { m with modulePins := m.modulePins.insert modName addr }

def addImportedEnv (m : IxImportMap) (addr : Address) : IxImportMap :=
  if m.importedEnvs.contains addr then m
  else { m with importedEnvs := m.importedEnvs.push addr }

def lookupName? (m : IxImportMap) (name : Ix.Name) : Option Address :=
  m.nameToAddr.get? name

def merge (m1 m2 : IxImportMap) : IxImportMap :=
  let nameToAddr := m2.nameToAddr.foldl (fun acc k v => acc.insert k v) m1.nameToAddr
  let modulePins := m2.modulePins.foldl (fun acc k v => acc.insert k v) m1.modulePins
  let importedEnvs := m2.importedEnvs.foldl (fun acc a =>
    if acc.contains a then acc else acc.push a) m1.importedEnvs
  { nameToAddr, modulePins, importedEnvs }

end IxImportMap

/-! ## Lexical Scope Stack (`namespace`, `section`, `open`, `variable`, `universe`) -/

/-- An `open` directive in lexical scope. -/
inductive OpenDecl where
  | simple (ns : Ix.Name) (only : List Ix.Name := [])
  | explicit (aliasName : Ix.Name) (declName : Ix.Name)
  deriving BEq, Repr, Inhabited

/-- Frozen lexical scope snapshot attached to a top-level declaration. -/
structure ScopeSnapshot where
  currNamespace : Ix.Name         := Name.mkAnon
  openDecls     : List OpenDecl   := []
  levelNames    : List Ix.Name    := []
  varBinders    : Array Ix.Syntax := #[]
  isPrivate     : Bool            := false
  isProtected   : Bool            := false
  deriving Repr, Inhabited

/-- Mutable frame pushed by `namespace` or `section` during Pass 1 scanning. -/
structure ScopeFrame where
  header        : Ix.Name
  isNamespace   : Bool
  savedScope    : ScopeSnapshot
  deriving Repr, Inhabited

/-! ## Top-Level Declaration Kind & `ModuleDecl` -/

inductive DeclKind where
  | defn
  | abbrev
  | thm
  | axiomDecl
  | opaqueDecl
  | inst
  | ind
  | struct
  | cls
  deriving BEq, DecidableEq, Repr, Inhabited

/-- A top-level declaration collected in Pass 1, with its lexical `ScopeSnapshot`. -/
structure ModuleDecl where
  idx        : Nat
  kind       : DeclKind
  shortName  : Ix.Name
  fullName   : Ix.Name
  univParams : List Ix.Name
  scope      : ScopeSnapshot
  stx        : Ix.Syntax
  ctorNames  : List Ix.Name := []
  fieldNames : List Ix.Name := []
  deriving Repr, Inhabited

/-- Module-wide symbol table built in Pass 1 before any elaboration or reference resolution.
    Pre-registers all inductive constructors and structure fields so forward pattern-matching
    and dot-notation work regardless of declaration order in the file. -/
structure ModuleIndex where
  decls         : Array ModuleDecl         := #[]
  declByName    : NameMap Nat              := NameMap.empty
  ctorToInd     : NameMap (Ix.Name × Nat)  := NameMap.empty
  fieldToStruct : NameMap (Ix.Name × Nat)  := NameMap.empty
  auxToInd      : NameMap (Ix.Name × Nat)  := NameMap.empty
  importMap     : IxImportMap              := IxImportMap.empty
  deriving Repr, Inhabited

namespace ModuleIndex

/-- Look up the declaration index in `decls` that defines or owns `name`
    (checking primary declarations, constructors, structure fields, and recursors/auxiliaries). -/
def findOwnerIdx? (idx : ModuleIndex) (name : Ix.Name) : Option Nat :=
  match idx.declByName.get? name with
  | some dIdx => some dIdx
  | none =>
    match idx.ctorToInd.get? name with
    | some (_, dIdx) => some dIdx
    | none =>
      match idx.fieldToStruct.get? name with
      | some (_, dIdx) => some dIdx
      | none =>
        match idx.auxToInd.get? name with
        | some (_, dIdx) => some dIdx
        | none => none

/-- True if `name` is a known symbol in this module (or its `importMap`). -/
def containsSymbol (idx : ModuleIndex) (name : Ix.Name) : Bool :=
  (idx.findOwnerIdx? name).isSome || (idx.importMap.lookupName? name).isSome

/-- True if `name` is a constructor declared anywhere in this module. -/
def isModuleCtor (idx : ModuleIndex) (name : Ix.Name) : Bool :=
  idx.ctorToInd.contains name

end ModuleIndex

/-! ## Pass 1: Extracting Declarations, Constructors, Fields, and Build Maps -/

/-- Extract modifier flags `(isPrivate, isProtected)` from a `modifiersKind` syntax node. -/
def extractModifierFlags (modStx : Ix.Syntax) : Bool × Bool :=
  (Syntax.getArgs modStx).toList.foldl (fun (priv, prot) atom =>
    let v := Syntax.getAtomVal atom
    (priv || v == "private", prot || v == "protected")) (false, false)

/-- Extract explicit `.{u, v}` universe parameter names from a `univParamsKind` syntax node. -/
def extractUnivParams (uStx : Ix.Syntax) : List Ix.Name :=
  (Syntax.getArgs uStx).toList.map Syntax.getId |>.filter (!Name.isAnonymous ·)

/-- Extract constructor full names `fullIndName ++ ctorShortName` from a `null` node of `ctorDecl`s. -/
def extractCtorNames (fullIndName : Ix.Name) (ctorsStx : Ix.Syntax) : List Ix.Name :=
  (Syntax.getArgs ctorsStx).toList.filterMap fun ctorStx =>
    if Syntax.isOfKind ctorStx SyntaxKind.ctorDecl then
      let shortId := Syntax.getId (Syntax.getArg ctorStx 1)
      if Name.isAnonymous shortId then none
      else some (Name.append fullIndName shortId)
    else
      none

/-- Extract structure/class field full names `fullStructName ++ fieldShortName` from a `null` node of `fieldDecl`s. -/
def extractFieldNames (fullStructName : Ix.Name) (fieldsStx : Ix.Syntax) : List Ix.Name :=
  (Syntax.getArgs fieldsStx).toList.flatMap fun fieldStx =>
    if Syntax.isOfKind fieldStx SyntaxKind.fieldDecl then
      let args := Syntax.getArgs fieldStx
      -- For `(bPref ids : vPref ty)` args[0] is `(`, args[2] is `ids`; for bare `bPref ids : ...`, args[1] is `ids`
      let idsNode := match args[0]? with
        | some (.atom _ "(") | some (.atom _ "{") => Syntax.getArg fieldStx 2
        | _ => Syntax.getArg fieldStx 1
      (Syntax.getArgs idsNode).toList.filterMap fun idStx =>
        let shortId := Syntax.getId idStx
        if Name.isAnonymous shortId then none
        else some (Name.append fullStructName shortId)
    else
      []

/-- Standard reserved auxiliary suffixes generated for every inductive/structure/class `T`. -/
def standardIndAuxSuffixes : List String :=
  ["rec", "recOn", "casesOn", "below", "brecOn", "noConfusion", "noConfusionType", "_ctorIdx", "_sizeOf_inst"]

/-- Register a `ModuleDecl` and its constructors, fields, and auxiliaries into `ModuleIndex`. -/
def ModuleIndex.registerDecl (idx : ModuleIndex) (d : ModuleDecl) : ModuleIndex :=
  let dIdx := idx.decls.size
  let d := { d with idx := dIdx }
  let decls := idx.decls.push d
  let declByName := idx.declByName.insert d.fullName dIdx
  let ctorToInd := d.ctorNames.foldl (fun acc c => acc.insert c (d.fullName, dIdx)) idx.ctorToInd
  let fieldToStruct := d.fieldNames.foldl (fun acc f => acc.insert f (d.fullName, dIdx)) idx.fieldToStruct
  let auxToInd :=
    if d.kind == .ind || d.kind == .struct || d.kind == .cls then
      standardIndAuxSuffixes.foldl
        (fun acc suf => acc.insert (Name.mkStr d.fullName suf) (d.fullName, dIdx))
        idx.auxToInd
    else
      idx.auxToInd
  { idx with decls, declByName, ctorToInd, fieldToStruct, auxToInd }

/-- State of the Pass 1 lexical scanner. -/
structure ScopePassState where
  currScope : ScopeSnapshot   := {}
  frames    : List ScopeFrame := []
  modIdx    : ModuleIndex     := {}
  anonCount : Nat             := 0
  deriving Repr, Inhabited

/-- Process a single top-level command in Pass 1 (structurally recursive on `fuel` for `mutual ... end`). -/
def processCommandPass1 : Nat → Ix.Syntax → ScopePassState → Except String ScopePassState
  | 0, _, st => .ok st
  | fuel + 1, cmd, st => do
    let k := Syntax.getKind cmd
    -- 1. `import #<hash>`
    if k == SyntaxKind.hashImport then
      let hashNode := Syntax.getArg cmd 1
      let hexStr := Syntax.getAtomVal (Syntax.getArg hashNode 0)
      match parseHexAddress hexStr with
      | some addr =>
        return { st with modIdx := { st.modIdx with importMap := st.modIdx.importMap.addImportedEnv addr } }
      | none =>
        throw s!"invalid 64-hex-char content address '#{hexStr}' in import"
    -- 2. `import Mod [@ #<hash>]`
    else if k == SyntaxKind.importDecl then
      let modName := Syntax.getId (Syntax.getArg cmd 1)
      let pinNode := Syntax.getArg cmd 2
      if Syntax.isOfKind pinNode SyntaxKind.hashRef then
        let hexStr := Syntax.getAtomVal (Syntax.getArg pinNode 0)
        match parseHexAddress hexStr with
        | some addr =>
          return { st with modIdx := { st.modIdx with importMap := st.modIdx.importMap.insertModulePin modName addr } }
        | none =>
          throw s!"invalid 64-hex-char content address '#{hexStr}' in import pin"
      else
        return st
    -- 3. `map Foo.Bar := #<hash>`
    else if k == SyntaxKind.buildMapDecl then
      let symName := Syntax.getId (Syntax.getArg cmd 1)
      let hashNode := Syntax.getArg cmd 3
      let hexStr := Syntax.getAtomVal (Syntax.getArg hashNode 0)
      match parseHexAddress hexStr with
      | some addr =>
        return { st with modIdx := { st.modIdx with importMap := st.modIdx.importMap.insertName symName addr } }
      | none =>
        throw s!"invalid 64-hex-char content address '#{hexStr}' in map declaration"
    -- 4. `namespace Foo.Bar`
    else if k == SyntaxKind.namespaceDecl then
      let ns := Syntax.getId (Syntax.getArg cmd 1)
      let newNs := Name.append st.currScope.currNamespace ns
      let frame : ScopeFrame := { header := ns, isNamespace := true, savedScope := st.currScope }
      let newOpen : OpenDecl := .simple newNs []
      let newScope := { st.currScope with
        currNamespace := newNs
        openDecls := newOpen :: st.currScope.openDecls }
      return { st with currScope := newScope, frames := frame :: st.frames }
    -- 5. `section [Foo]`
    else if k == SyntaxKind.sectionDecl then
      let secId := match Syntax.getOptional? (Syntax.getArg cmd 1) with
        | some idStx => Syntax.getId idStx
        | none => Name.mkAnon
      let frame : ScopeFrame := { header := secId, isNamespace := false, savedScope := st.currScope }
      return { st with frames := frame :: st.frames }
    -- 6. `end [Foo]`
    else if k == SyntaxKind.endDecl then
      match st.frames with
      | [] => throw "unmatched 'end' command"
      | frame :: rest =>
        return { st with currScope := frame.savedScope, frames := rest }
    -- 7. `universe u v`
    else if k == SyntaxKind.universeDecl then
      let uIds := (Syntax.getArgs (Syntax.getArg cmd 1)).toList.map Syntax.getId
      let newLvls := (st.currScope.levelNames ++ uIds).eraseDups
      return { st with currScope := { st.currScope with levelNames := newLvls } }
    -- 8. `variable (x : A) ...`
    else if k == SyntaxKind.variableDecl then
      let newVars := Syntax.getArgs (Syntax.getArg cmd 1)
      return { st with currScope := { st.currScope with varBinders := st.currScope.varBinders ++ newVars } }
    -- 9. `open Foo.Bar [(a b)]`
    else if k == SyntaxKind.openDecl then
      let nss := (Syntax.getArgs (Syntax.getArg cmd 1)).toList.map Syntax.getId
      let onlyIds : List Ix.Name := match Syntax.getOptional? (Syntax.getArg cmd 2) with
        | some parenNode =>
          (Syntax.getArgs (Syntax.getArg parenNode 1)).toList.map Syntax.getId
        | none => []
      let newOpens := nss.map fun ns =>
        if onlyIds.isEmpty then OpenDecl.simple ns []
        else OpenDecl.simple ns onlyIds
      return { st with currScope := { st.currScope with openDecls := newOpens ++ st.currScope.openDecls } }
    -- 10. `mutual cmd1 cmd2 ... end` (flattened into individual declarations!)
    else if k == SyntaxKind.mutualDecl then
      let innerCmds := Syntax.getArgs (Syntax.getArg cmd 1)
      innerCmds.toList.foldlM (fun acc c => processCommandPass1 fuel c acc) st
    -- 11. Top-level declarations (`def`, `abbrev`, `theorem`, `axiom`, `opaque`, `instance`, `inductive`, `structure`, `class`)
    else if k == SyntaxKind.defDecl || k == SyntaxKind.abbrevDecl || k == SyntaxKind.theoremDecl ||
            k == SyntaxKind.opaqueDecl || k == SyntaxKind.axiomDecl || k == SyntaxKind.instanceDecl ||
            k == SyntaxKind.inductiveDecl || k == SyntaxKind.structureDecl || k == SyntaxKind.classDecl then
      let (isPriv, isProt) := extractModifierFlags (Syntax.getArg cmd 0)
      let rawId := Syntax.getId (Syntax.getArg cmd 2)
      let (shortName, anonCount') :=
        if Name.isAnonymous rawId then
          (Name.mkStr Name.mkAnon s!"_inst_{st.anonCount}", st.anonCount + 1)
        else
          (rawId, st.anonCount)
      let fullName := Name.append st.currScope.currNamespace shortName
      let explicitUnivs := extractUnivParams (Syntax.getArg cmd 3)
      let declScope := { st.currScope with isPrivate := isPriv, isProtected := isProt }
      let declKind : DeclKind :=
        if k == SyntaxKind.defDecl then .defn
        else if k == SyntaxKind.abbrevDecl then .abbrev
        else if k == SyntaxKind.theoremDecl then .thm
        else if k == SyntaxKind.axiomDecl then .axiomDecl
        else if k == SyntaxKind.opaqueDecl then .opaqueDecl
        else if k == SyntaxKind.instanceDecl then .inst
        else if k == SyntaxKind.inductiveDecl then .ind
        else if k == SyntaxKind.structureDecl then .struct
        else .cls
      let (ctorNames, fieldNames) :=
        if k == SyntaxKind.inductiveDecl then
          -- args: #[modifiers, "inductive", id, univParams, binders, vPref, optType, ctorsNull, derivingNull]
          let ctorsNode := Syntax.getArg cmd 7
          (extractCtorNames fullName ctorsNode, [])
        else if k == SyntaxKind.structureDecl || k == SyntaxKind.classDecl then
          -- args: #[modifiers, kw, id, univParams, binders, extendsNull, vPref, optType, customCtorOrNull, fieldsOrCtorsNull, derivingNull]
          let customCtorNode := Syntax.getArg cmd 8
          let fieldsOrCtorsNode := Syntax.getArg cmd 9
          let firstChild? := (Syntax.getArgs fieldsOrCtorsNode)[0]?
          match firstChild? with
          | some c0 =>
            if Syntax.isOfKind c0 SyntaxKind.ctorDecl then
              (extractCtorNames fullName fieldsOrCtorsNode, [])
            else
              let ctorShort :=
                let cid := Syntax.getId customCtorNode
                if Name.isAnonymous cid then Name.simple "mk" else cid
              let ctorFull := Name.append fullName ctorShort
              ([ctorFull], extractFieldNames fullName fieldsOrCtorsNode)
          | none =>
            let ctorShort :=
              let cid := Syntax.getId customCtorNode
              if Name.isAnonymous cid then Name.simple "mk" else cid
            let ctorFull := Name.append fullName ctorShort
            ([ctorFull], [])
        else
          ([], [])
      let decl : ModuleDecl :=
        { idx        := st.modIdx.decls.size
          kind       := declKind
          shortName  := shortName
          fullName   := fullName
          univParams := explicitUnivs
          scope      := declScope
          stx        := cmd
          ctorNames  := ctorNames
          fieldNames := fieldNames }
      return { st with
        modIdx    := st.modIdx.registerDecl decl
        anonCount := anonCount' }
    else
      -- Ignore notationDecl or unknown commands in Pass 1
      return st

/-- Run Pass 1 over a parsed module `Syntax` node (`SyntaxKind.moduleKind`) to build `ModuleIndex`. -/
def buildModuleIndex (moduleStx : Ix.Syntax) : Except String ModuleIndex := do
  let cmds := Syntax.getArgs moduleStx
  let finalState ← cmds.toList.foldlM (fun st cmd => processCommandPass1 64 cmd st) {}
  return finalState.modIdx

/-! ## Lexical Name Resolution (`resolveIdentInScope`) -/

/-- Return all namespace prefixes of `ns` from most specific (`ns`) to root (`Name.mkAnon`). -/
def namespacePrefixes : Ix.Name → List Ix.Name
  | .anonymous h => [.anonymous h]
  | n@(.str p _ _) => n :: namespacePrefixes p
  | n@(.num p _ _) => n :: namespacePrefixes p

/-- Resolve a surface identifier `id` under `scope : ScopeSnapshot` against `modIdx : ModuleIndex`
    and an external predicate `isExtConst : Ix.Name → Bool`.
    Returns all matching candidate full names in priority order. -/
def resolveNameCandidates (scope : ScopeSnapshot) (modIdx : ModuleIndex)
    (isExtConst : Ix.Name → Bool := fun _ => false) (id : Ix.Name) : List Ix.Name :=
  let isKnown (cand : Ix.Name) : Bool :=
    modIdx.containsSymbol cand || isExtConst cand
  -- 1. Walk enclosing namespaces from innermost (`currNamespace ++ id`) to root (`id`)
  let nsCands := (namespacePrefixes scope.currNamespace).filterMap fun pre =>
    let cand := Name.append pre id
    if isKnown cand then some cand else none
  -- 2. Check `open` declarations
  let openCands := scope.openDecls.filterMap fun od =>
    match od with
    | .simple ns only =>
      if !only.isEmpty && !only.contains id then none
      else
        let cand := Name.append ns id
        if isKnown cand then some cand else none
    | .explicit aliasName declName =>
      if id == aliasName && isKnown declName then some declName else none
  (nsCands ++ openCands).eraseDups

/-- Resolve `id` to its highest-priority candidate in `scope`, or `id` itself if unresolved
    (mapping the standard Mathlib/Lean unicode alias `ℕ` to `Nat` when `ℕ` is not locally declared). -/
def resolveIdentInScope (scope : ScopeSnapshot) (modIdx : ModuleIndex)
    (isExtConst : Ix.Name → Bool := fun _ => false) (id : Ix.Name) : Ix.Name :=
  match resolveNameCandidates scope modIdx isExtConst id with
  | best :: _ => best
  | []        => if id == Name.simple "ℕ" then Name.simple "Nat" else id

end Ix.Frontend
