/-
  Ix.Frontend.Scope: Pass 1 of the Ix Frontend — Lexical Scope Management,
  First-Class `Name -> Address` Build/Import Mapping (`IxImportMap`),
  and Pre-Elaboration Module Symbol Table (`ModuleIndex`).
-/
module

public import Ix.Frontend.Parser.Command

@[expose] public section

namespace Ix.Frontend

open Ix.Frontend.Parser

/-- Pure, proof-free, strictly-spine-evaluated Red-Black tree keyed by `Ix.Name`
    (using `Name.cmpStruct`, which reads no hash).
    Unlike `Std.TreeMap`, this type has zero wrapper structures (`TreeMap.mk` / `DTreeMap.mk`),
    zero `wf : Balanced` proof terms, zero `Nat` size multiplications, and strictly forces
    modified child subtrees before constructing parent `.node`s so call-by-name kernel
    reduction (`Whnf.lean`) never accumulates unevaluated `.insert` chains. -/
inductive NameMap (α : Type) where
  | leaf : NameMap α
  | node : Bool → Ix.Name → α → NameMap α → NameMap α → NameMap α
  deriving Repr, Inhabited

namespace NameMap

def empty : NameMap α := .leaf

def isEmpty : NameMap α → Bool
  | .leaf => true
  | .node .. => false

@[inline] def bindMap (m : NameMap α) (k : NameMap α → β) : β :=
  match m with
  | .leaf => k .leaf
  | .node c key val l r => k (.node c key val l r)

def get? : NameMap α → Ix.Name → Option α
  | .leaf, _ => none
  | .node _ k' v' l r, k =>
    match Name.cmpStruct k k' with
    | .lt => get? l k
    | .gt => get? r k
    | .eq => some v'

def contains : NameMap α → Ix.Name → Bool
  | .leaf, _ => false
  | .node _ k' _ l r, k =>
    match Name.cmpStruct k k' with
    | .lt => contains l k
    | .gt => contains r k
    | .eq => true

@[inline] def balanceLeft (c : Bool) (k : Ix.Name) (v : α) (l r : NameMap α) : NameMap α :=
  match c with
  | true => .node true k v l r
  | false =>
    match l with
    | .node true lk lv (.node true llk llv lll llr) lr =>
      .node true lk lv (.node false llk llv lll llr) (.node false k v lr r)
    | .node true lk lv ll (.node true lrk lrv lrl lrr) =>
      .node true lrk lrv (.node false lk lv ll lrl) (.node false k v lrr r)
    | _ => .node false k v l r

@[inline] def balanceRight (c : Bool) (k : Ix.Name) (v : α) (l r : NameMap α) : NameMap α :=
  match c with
  | true => .node true k v l r
  | false =>
    match r with
    | .node true rk rv (.node true rlk rlv rll rlr) rr =>
      .node true rlk rlv (.node false k v l rll) (.node false rk rv rlr rr)
    | .node true rk rv rl (.node true rrk rrv rrl rrr) =>
      .node true rk rv (.node false k v l rl) (.node false rrk rrv rrl rrr)
    | _ => .node false k v l r

def ins (k : Ix.Name) (v : α) : NameMap α → NameMap α
  | .leaf => .node true k v .leaf .leaf
  | .node c k' v' l r =>
    match Name.cmpStruct k k' with
    | .lt =>
      match ins k v l with
      | .leaf => .leaf
      | l'@(.node ..) => balanceLeft c k' v' l' r
    | .gt =>
      match ins k v r with
      | .leaf => .leaf
      | r'@(.node ..) => balanceRight c k' v' l r'
    | .eq => .node c k v l r

def insert (m : NameMap α) (k : Ix.Name) (v : α) : NameMap α :=
  match ins k v m with
  | .leaf => .leaf
  | .node _ k' v' l r => .node false k' v' l r

def foldl (m : NameMap α) (f : β → Ix.Name → α → β) (init : β) : β :=
  match m with
  | .leaf => init
  | .node _ k v l r =>
    let acc1 := foldl l f init
    let acc2 := f acc1 k v
    foldl r f acc2

def toListAux : NameMap α → List (Ix.Name × α) → List (Ix.Name × α)
  | .leaf, acc => acc
  | .node _ k v l r, acc => toListAux l ((k, v) :: toListAux r acc)

def toList (m : NameMap α) : List (Ix.Name × α) :=
  toListAux m []

def size : NameMap α → Nat
  | .leaf => 0
  | .node _ _ _ l r => 1 + size l + size r

end NameMap

/-- Pure, proof-free, strictly-spine-evaluated Red-Black set of `Ix.Name`s. -/
inductive NameSet where
  | leaf : NameSet
  | node : Bool → Ix.Name → NameSet → NameSet → NameSet
  deriving Repr, Inhabited

namespace NameSet

def empty : NameSet := .leaf

def isEmpty : NameSet → Bool
  | .leaf => true
  | .node .. => false

@[inline] def bindSet (s : NameSet) (k : NameSet → β) : β :=
  match s with
  | .leaf => k .leaf
  | .node c key l r => k (.node c key l r)

def contains : NameSet → Ix.Name → Bool
  | .leaf, _ => false
  | .node _ k' l r, k =>
    match Name.cmpStruct k k' with
    | .lt => contains l k
    | .gt => contains r k
    | .eq => true

@[inline] def balanceLeft (c : Bool) (k : Ix.Name) (l r : NameSet) : NameSet :=
  match c with
  | true => .node true k l r
  | false =>
    match l with
    | .node true lk (.node true llk lll llr) lr =>
      .node true lk (.node false llk lll llr) (.node false k lr r)
    | .node true lk ll (.node true lrk lrl lrr) =>
      .node true lrk (.node false lk ll lrl) (.node false k lrr r)
    | _ => .node false k l r

@[inline] def balanceRight (c : Bool) (k : Ix.Name) (l r : NameSet) : NameSet :=
  match c with
  | true => .node true k l r
  | false =>
    match r with
    | .node true rk (.node true rlk rll rlr) rr =>
      .node true rlk (.node false k l rll) (.node false rk rlr rr)
    | .node true rk rl (.node true rrk rrl rrr) =>
      .node true rk (.node false k l rl) (.node false rrk rrl rrr)
    | _ => .node false k l r

def ins (k : Ix.Name) : NameSet → NameSet
  | .leaf => .node true k .leaf .leaf
  | .node c k' l r =>
    match Name.cmpStruct k k' with
    | .lt =>
      match ins k l with
      | .leaf => .leaf
      | l'@(.node ..) => balanceLeft c k' l' r
    | .gt =>
      match ins k r with
      | .leaf => .leaf
      | r'@(.node ..) => balanceRight c k' l r'
    | .eq => .node c k' l r

def insert (s : NameSet) (k : Ix.Name) : NameSet :=
  match ins k s with
  | .leaf => .leaf
  | .node _ k' l r => .node false k' l r

def foldl (s : NameSet) (f : β → Ix.Name → β) (init : β) : β :=
  match s with
  | .leaf => init
  | .node _ k l r =>
    let acc1 := foldl l f init
    let acc2 := f acc1 k
    foldl r f acc2

def toListAux : NameSet → List Ix.Name → List Ix.Name
  | .leaf, acc => acc
  | .node _ k l r, acc => toListAux l (k :: toListAux r acc)

def toList (s : NameSet) : List Ix.Name :=
  toListAux s []

def size : NameSet → Nat
  | .leaf => 0
  | .node _ _ l r => 1 + size l + size r

end NameSet

/-! ## Hex Address Decoding & First-Class `IxImportMap` -/

/-- Parse a 64-character hex string into a 32-byte `Address`. -/
def parseHexBytesAux : List Char → List UInt8 → Nat → Option ByteArray
  | [], revAcc, cnt =>
    if Nat.beq cnt 32 then some ⟨Array.mk revAcc.reverse⟩ else none
  | c1 :: c2 :: rest, revAcc, cnt => do
    let hi ← natOfHex c1
    let lo ← natOfHex c2
    let byte : UInt8 := UInt8.ofNat (hi * 16 + lo)
    let cnt' := cnt + 1
    if Nat.beq cnt' 0 then parseHexBytesAux rest (byte :: revAcc) 0
    else parseHexBytesAux rest (byte :: revAcc) cnt'
  | _, _, _ => none

def parseHexAddress (hex : String) : Option Address := do
  let ba ← parseHexBytesAux hex.toList [] 0
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
  match m with
  | ⟨nameToAddr, modulePins, importedEnvs⟩ =>
    (nameToAddr.insert name addr).bindMap fun nameToAddr' =>
      ⟨nameToAddr', modulePins, importedEnvs⟩

def insertModulePin (m : IxImportMap) (modName : Ix.Name) (addr : Address) : IxImportMap :=
  match m with
  | ⟨nameToAddr, modulePins, importedEnvs⟩ =>
    (modulePins.insert modName addr).bindMap fun modulePins' =>
      ⟨nameToAddr, modulePins', importedEnvs⟩

def addImportedEnv (m : IxImportMap) (addr : Address) : IxImportMap :=
  match m with
  | ⟨nameToAddr, modulePins, importedEnvs⟩ =>
    if importedEnvs.contains addr then m
    else ⟨nameToAddr, modulePins, importedEnvs.push addr⟩

def lookupName? (m : IxImportMap) (name : Ix.Name) : Option Address :=
  m.nameToAddr.get? name

def merge (m1 m2 : IxImportMap) : IxImportMap :=
  let nameToAddr := m2.nameToAddr.foldl (fun acc k v => acc.insert k v) m1.nameToAddr
  let modulePins := m2.modulePins.foldl (fun acc k v => acc.insert k v) m1.modulePins
  let importedEnvs := m2.importedEnvs.foldl (fun acc a =>
    if acc.contains a then acc else acc.push a) m1.importedEnvs
  nameToAddr.bindMap fun nameToAddr' =>
  modulePins.bindMap fun modulePins' =>
    { nameToAddr := nameToAddr', modulePins := modulePins', importedEnvs }

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
  macroRules    : Array MacroRule          := #[]
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

/-- Return all conflict variants `(tag, variantFullName)` in `idx` for `origName`
    (i.e. declarations named `origName.#merge.<tag>`). -/
def findConflictVariants (idx : ModuleIndex) (origName : Ix.Name) : List (String × Ix.Name) :=
  idx.decls.toList.filterMap fun d =>
    match Name.splitMergeVariant? d.fullName with
    | some (orig, tag, []) => if orig == origName then some (tag, d.fullName) else none
    | _ => none

/-- Return all conflicted original declaration names in `idx` in appearance order. -/
def conflictedNames (idx : ModuleIndex) : List Ix.Name :=
  (idx.decls.toList.filterMap fun d =>
    match Name.splitMergeVariant? d.fullName with
    | some (orig, _, []) => some orig
    | _ => none).eraseDups

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

/-- Register a `ModuleDecl` at index `dIdx` and its constructors, fields, and auxiliaries
    into `ModuleIndex`'s `NameMap` tables (deferring `Array.mk revDecls.reverse` to `buildModuleIndex`). -/
def ModuleIndex.registerDeclMaps (idx : ModuleIndex) (dIdx : Nat) (d : ModuleDecl) : ModuleIndex :=
  match idx with
  | ⟨decls, declByName0, ctorToInd0, fieldToStruct0, auxToInd0, importMap, macroRules⟩ =>
    let declByName := declByName0.insert d.fullName dIdx
    if d.kind != .ind && d.kind != .struct && d.kind != .cls then
      declByName.bindMap fun declByName' =>
        ⟨decls, declByName', ctorToInd0, fieldToStruct0, auxToInd0, importMap, macroRules⟩
    else
      let ctorToInd := d.ctorNames.foldl (fun acc c => acc.insert c (d.fullName, dIdx)) ctorToInd0
      let fieldToStruct := d.fieldNames.foldl (fun acc f => acc.insert f (d.fullName, dIdx)) fieldToStruct0
      let auxToInd :=
        standardIndAuxSuffixes.foldl
          (fun acc suf => acc.insert (Name.mkStr d.fullName suf) (d.fullName, dIdx))
          auxToInd0
      declByName.bindMap fun declByName' =>
      ctorToInd.bindMap fun ctorToInd' =>
      fieldToStruct.bindMap fun fieldToStruct' =>
      auxToInd.bindMap fun auxToInd' =>
        ⟨decls, declByName', ctorToInd', fieldToStruct', auxToInd', importMap, macroRules⟩

/-- Register a `ModuleDecl` and its constructors, fields, and auxiliaries into `ModuleIndex`. -/
def ModuleIndex.registerDecl (idx : ModuleIndex) (d : ModuleDecl) : ModuleIndex :=
  let dIdx := idx.decls.size
  let d := { d with idx := dIdx }
  let idx' := idx.registerDeclMaps dIdx d
  { idx' with decls := idx.decls.push d }

/-- State of the Pass 1 lexical scanner. -/
structure ScopePassState where
  currScope : ScopeSnapshot   := {}
  frames    : List ScopeFrame := []
  modIdx    : ModuleIndex     := {}
  revDecls  : List ModuleDecl := []
  declCount : Nat             := 0
  anonCount : Nat             := 0
  deriving Repr, Inhabited

/-- Process a single top-level command in Pass 1 (structurally recursive on `fuel` for `mutual ... end`). -/
def processCommandPass1 : Nat → Ix.Syntax → ScopePassState → Except String ScopePassState
  | 0, _, st => .ok st
  | fuel + 1, cmd, st => do
    match st with
    | ⟨currScope, frames, modIdx, revDecls, declCount, anonCount⟩ =>
      let k := Syntax.getKind cmd
      -- 1. `import #<hash>`
      if k == SyntaxKind.hashImport then
        let hashNode := Syntax.getArg cmd 1
        let hexStr := Syntax.getAtomVal (Syntax.getArg hashNode 0)
        match parseHexAddress hexStr with
        | some addr =>
          match modIdx with
          | ⟨decls, declByName, ctorToInd, fieldToStruct, auxToInd, importMap, macroRules⟩ =>
            return ⟨currScope, frames,
              ⟨decls, declByName, ctorToInd, fieldToStruct, auxToInd, importMap.addImportedEnv addr, macroRules⟩,
              revDecls, declCount, anonCount⟩
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
            match modIdx with
            | ⟨decls, declByName, ctorToInd, fieldToStruct, auxToInd, importMap, macroRules⟩ =>
              return ⟨currScope, frames,
                ⟨decls, declByName, ctorToInd, fieldToStruct, auxToInd, importMap.insertModulePin modName addr, macroRules⟩,
                revDecls, declCount, anonCount⟩
          | none =>
            throw s!"invalid 64-hex-char content address '#{hexStr}' in import pin"
        else
          return ⟨currScope, frames, modIdx, revDecls, declCount, anonCount⟩
      -- 3. `map Foo.Bar := #<hash>`
      else if k == SyntaxKind.buildMapDecl then
        let symName := Syntax.getId (Syntax.getArg cmd 1)
        let hashNode := Syntax.getArg cmd 3
        let hexStr := Syntax.getAtomVal (Syntax.getArg hashNode 0)
        match parseHexAddress hexStr with
        | some addr =>
          match modIdx with
          | ⟨decls, declByName, ctorToInd, fieldToStruct, auxToInd, importMap, macroRules⟩ =>
            return ⟨currScope, frames,
              ⟨decls, declByName, ctorToInd, fieldToStruct, auxToInd, importMap.insertName symName addr, macroRules⟩,
              revDecls, declCount, anonCount⟩
        | none =>
          throw s!"invalid 64-hex-char content address '#{hexStr}' in map declaration"
      -- 4. `namespace Foo.Bar`
      else if k == SyntaxKind.namespaceDecl then
        let ns := Syntax.getId (Syntax.getArg cmd 1)
        let newNs := Name.append currScope.currNamespace ns
        let frame : ScopeFrame := { header := ns, isNamespace := true, savedScope := currScope }
        let newOpen : OpenDecl := .simple newNs []
        let newScope : ScopeSnapshot := { currScope with
          currNamespace := newNs
          openDecls := newOpen :: currScope.openDecls }
        return ⟨newScope, frame :: frames, modIdx, revDecls, declCount, anonCount⟩
      -- 5. `section [Foo]`
      else if k == SyntaxKind.sectionDecl then
        let secId := match Syntax.getOptional? (Syntax.getArg cmd 1) with
          | some idStx => Syntax.getId idStx
          | none => Name.mkAnon
        let frame : ScopeFrame := { header := secId, isNamespace := false, savedScope := currScope }
        return ⟨currScope, frame :: frames, modIdx, revDecls, declCount, anonCount⟩
      -- 6. `end [Foo]`
      else if k == SyntaxKind.endDecl then
        match frames with
        | [] => throw "unmatched 'end' command"
        | frame :: rest =>
          return ⟨frame.savedScope, rest, modIdx, revDecls, declCount, anonCount⟩
      -- 7. `universe u v`
      else if k == SyntaxKind.universeDecl then
        let uIds := (Syntax.getArgs (Syntax.getArg cmd 1)).toList.map Syntax.getId
        let newLvls := (currScope.levelNames ++ uIds).eraseDups
        return ⟨{ currScope with levelNames := newLvls }, frames, modIdx, revDecls, declCount, anonCount⟩
      -- 8. `variable (x : A) ...`
      else if k == SyntaxKind.variableDecl then
        let newVars := Syntax.getArgs (Syntax.getArg cmd 1)
        return ⟨{ currScope with varBinders := currScope.varBinders ++ newVars }, frames, modIdx, revDecls, declCount, anonCount⟩
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
        return ⟨{ currScope with openDecls := newOpens ++ currScope.openDecls }, frames, modIdx, revDecls, declCount, anonCount⟩
      -- 10. `mutual cmd1 cmd2 ... end` (flattened into individual declarations!)
      else if k == SyntaxKind.mutualDecl then
        let innerCmds := Syntax.getArgs (Syntax.getArg cmd 1)
        innerCmds.toList.foldlM (fun acc c => processCommandPass1 fuel c acc)
          ⟨currScope, frames, modIdx, revDecls, declCount, anonCount⟩
      -- 10b. `#merge | tag1 => cmd1 | tag2 => cmd2 ... end` (first-class conflict block)
      else if k == SyntaxKind.mergeConflictDecl then
        let arms := Syntax.getArgs (Syntax.getArg cmd 1)
        arms.toList.foldlM (fun acc arm => do
          let tagId := Syntax.getId (Syntax.getArg arm 1)
          let tagStr := Name.toStringTotal tagId
          let innerCmd := Syntax.getArg arm 3
          let innerCmd' := match innerCmd with
            | .node info ik iargs =>
              match iargs.toList with
              | a0 :: a1 :: a2 :: rest =>
                let rawId := Syntax.getId a2
                if !Name.isAnonymous rawId && !Name.isMergeConflict rawId then
                  let mergedId := Name.mkMergeVariant rawId tagStr
                  .node info ik (Array.mk (a0 :: a1 :: Syntax.mkSimpleIdent mergedId :: rest))
                else innerCmd
              | _ => innerCmd
            | _ => innerCmd
          processCommandPass1 fuel innerCmd' acc)
          ⟨currScope, frames, modIdx, revDecls, declCount, anonCount⟩
      -- 11. Top-level declarations (`def`, `abbrev`, `theorem`, `axiom`, `opaque`, `instance`, `inductive`, `structure`, `class`)
      else if k == SyntaxKind.defDecl || k == SyntaxKind.abbrevDecl || k == SyntaxKind.theoremDecl ||
              k == SyntaxKind.opaqueDecl || k == SyntaxKind.axiomDecl || k == SyntaxKind.instanceDecl ||
              k == SyntaxKind.inductiveDecl || k == SyntaxKind.structureDecl || k == SyntaxKind.classDecl then
        let (isPriv, isProt) := extractModifierFlags (Syntax.getArg cmd 0)
        let rawId := Syntax.getId (Syntax.getArg cmd 2)
        let (shortName, anonCount') :=
          if Name.isAnonymous rawId then
            (Name.mkStr Name.mkAnon s!"_inst_{anonCount}", anonCount + 1)
          else
            (rawId, anonCount)
        let fullName := Name.append currScope.currNamespace shortName
        let explicitUnivs := extractUnivParams (Syntax.getArg cmd 3)
        let declScope := { currScope with isPrivate := isPriv, isProtected := isProt }
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
          { idx        := declCount
            kind       := declKind
            shortName  := shortName
            fullName   := fullName
            univParams := explicitUnivs
            scope      := declScope
            stx        := cmd
            ctorNames  := ctorNames
            fieldNames := fieldNames }
        let modIdx' := modIdx.registerDeclMaps declCount decl
        InputContext.bindNat (declCount + 1) fun nextDeclCount' =>
          return ⟨currScope, frames, modIdx', decl :: revDecls, nextDeclCount', anonCount'⟩
      else if k == SyntaxKind.notationDecl || k == SyntaxKind.macroDecl then
        let (_, mRules) := decodeNotationOrMacroDecl cmd
        if mRules.isEmpty then
          return ⟨currScope, frames, modIdx, revDecls, declCount, anonCount⟩
        else
          match modIdx with
          | ⟨decls, declByName, ctorToInd, fieldToStruct, auxToInd, importMap, macroRules⟩ =>
            return ⟨currScope, frames,
              ⟨decls, declByName, ctorToInd, fieldToStruct, auxToInd, importMap, macroRules ++ Array.mk mRules⟩,
              revDecls, declCount, anonCount⟩
      else
        -- Ignore unknown commands in Pass 1
        return ⟨currScope, frames, modIdx, revDecls, declCount, anonCount⟩

/-- Run Pass 1 over a parsed module `Syntax` node (`SyntaxKind.moduleKind`) to build `ModuleIndex`. -/
def buildModuleIndex (moduleStx : Ix.Syntax) : Except String ModuleIndex := do
  let cmds := Syntax.getArgs moduleStx
  let finalState ← cmds.toList.foldlM (fun st cmd => processCommandPass1 64 cmd st) {}
  match finalState.modIdx with
  | ⟨_, declByName, ctorToInd, fieldToStruct, auxToInd, importMap, macroRules⟩ =>
    let declList := match finalState.revDecls.reverse with | [] => [] | d :: ds => d :: ds
    return ⟨Array.mk declList, declByName, ctorToInd, fieldToStruct, auxToInd, importMap, macroRules⟩

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
  if (match scope.currNamespace with | .anonymous _ => true | _ => false) && scope.openDecls.isEmpty then
    if id == Name.simple "ℕ" then
      if modIdx.containsSymbol id || isExtConst id then id else Name.simple "Nat"
    else
      id
  else
    match resolveNameCandidates scope modIdx isExtConst id with
    | best :: _ => best
    | []        => if id == Name.simple "ℕ" then Name.simple "Nat" else id

end Ix.Frontend
