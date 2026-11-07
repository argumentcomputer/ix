import Aiur.Modules.Check
import Aiur.Generic.Frontend

namespace Aiur.Modules.Frontend
open Lean Elab Term
open Aiur.Frontend
open Aiur.Generic.Frontend

declare_syntax_cat aiur_module_ref (behavior := symbol)
declare_syntax_cat aiur_qualified (behavior := symbol)
declare_syntax_cat aiur_global_name (behavior := symbol)
declare_syntax_cat aiur_signature_member (behavior := symbol)
declare_syntax_cat aiur_module_parameter (behavior := symbol)
declare_syntax_cat aiur_root_decl (behavior := symbol)
declare_syntax_cat aiur_modules (behavior := symbol)
declare_syntax_cat aiur_module_member (behavior := symbol)

syntax (name := refName) ident : aiur_module_ref
syntax (name := refApply) ident "::<" sepBy1(aiur_module_ref, ",", ",", allowTrailingSep) closeAngle : aiur_module_ref
syntax (name := qualified) aiur_module_ref "::" sepBy1(ident, "::") : aiur_qualified
syntax (name := rootedQualified) "::" aiur_module_ref "::" sepBy1(ident, "::") : aiur_qualified
syntax (name := globalName) ident : aiur_global_name
syntax (name := qualifiedName) aiur_qualified : aiur_global_name
syntax (name := qualifiedType) aiur_qualified : aiur_type
syntax (name := qualifiedAppliedType) aiur_qualified "<" sepBy1(aiur_type, ",", ",", allowTrailingSep) closeAngle : aiur_type
syntax (name := qualifiedValue) aiur_qualified : aiur_expr
syntax (name := qualifiedCall) aiur_qualified "(" sepBy(aiur_expr, ",", ",", allowTrailingSep) ")" : aiur_expr
syntax (name := qualifiedGenericCall) aiur_qualified "::<" sepBy1(aiur_type, ",", ",", allowTrailingSep) closeAngle
  "(" sepBy(aiur_expr, ",", ",", allowTrailingSep) ")" : aiur_expr
syntax (name := qualifiedGenericConstructor) aiur_qualified "::<" sepBy1(aiur_type, ",", ",", allowTrailingSep) closeAngle "::" ident : aiur_expr
syntax (name := qualifiedGenericConstructorArgs) aiur_qualified "::<" sepBy1(aiur_type, ",", ",", allowTrailingSep) closeAngle "::" ident
  "(" sepBy(aiur_expr, ",", ",", allowTrailingSep) ")" : aiur_expr
syntax (name := qualifiedRecord) atomic(aiur_qualified "{" sepBy(aiur_record_value, ",", ",", allowTrailingSep) "}") : aiur_expr
syntax (name := qualifiedGenericRecord) atomic(aiur_qualified "::<" sepBy1(aiur_type, ",", ",", allowTrailingSep) closeAngle
  "{" sepBy(aiur_record_value, ",", ",", allowTrailingSep) "}") : aiur_expr
syntax (name := qualifiedPattern) aiur_qualified : aiur_pattern
syntax (name := qualifiedPatternArgs) aiur_qualified "(" sepBy(aiur_pattern, ",", ",", allowTrailingSep) ")" : aiur_pattern
syntax (name := qualifiedGenericPattern) aiur_qualified "::<" sepBy1(aiur_type, ",", ",", allowTrailingSep) closeAngle "::" ident : aiur_pattern
syntax (name := qualifiedGenericPatternArgs) aiur_qualified "::<" sepBy1(aiur_type, ",", ",", allowTrailingSep) closeAngle "::" ident
  "(" sepBy(aiur_pattern, ",", ",", allowTrailingSep) ")" : aiur_pattern
syntax (name := qualifiedRecordPattern) aiur_qualified "{" aiur_record_patterns "}" : aiur_pattern
syntax (name := qualifiedGenericRecordPattern) aiur_qualified "::<" sepBy1(aiur_type, ",", ",", allowTrailingSep) closeAngle
  "{" aiur_record_patterns "}" : aiur_pattern
syntax (name := rootedCall) "::" ident "(" sepBy(aiur_expr, ",", ",", allowTrailingSep) ")" : aiur_expr
syntax (name := rootedGenericCall) "::" ident "::<" sepBy1(aiur_type, ",", ",", allowTrailingSep) closeAngle
  "(" sepBy(aiur_expr, ",", ",", allowTrailingSep) ")" : aiur_expr
syntax (name := rootedType) "::" ident : aiur_type
syntax (name := typedConst) &"const" ident ":" aiur_type "=" aiur_expr ";" : aiur_const
syntax (name := qualifiedMap) &"map" ident "(" sepBy(aiur_param, ",", ",", allowTrailingSep) ")"
  "->" aiur_type "=" aiur_global_name "=>" aiur_global_name ";" : aiur_map

syntax (name := sigAbstract) &"type" ident ";" : aiur_signature_member
syntax (name := sigGenericAbstract) &"type" ident "<" sepBy1(ident, ",", ",", allowTrailingSep) closeAngle ";" : aiur_signature_member
syntax (name := sigOpaqueAbstract) &"opaque" &"type" ident ";" : aiur_signature_member
syntax (name := sigGenericOpaqueAbstract) &"opaque" &"type" ident "<" sepBy1(ident, ",", ",", allowTrailingSep) closeAngle ";" : aiur_signature_member
syntax (name := sigAlias) aiur_alias : aiur_signature_member
syntax (name := sigConst) &"const" ident ":" aiur_type ";" : aiur_signature_member
syntax (name := sigTable) &"table" ident ":" aiur_type ";" : aiur_signature_member
syntax (name := sigFunction) "fn" ident "(" sepBy(aiur_param, ",", ",", allowTrailingSep) ")" "->" aiur_type ";" : aiur_signature_member
syntax (name := sigGenericFunction) "fn" ident "<" sepBy1(ident, ",", ",", allowTrailingSep) closeAngle
  "(" sepBy(aiur_param, ",", ",", allowTrailingSep) ")" "->" aiur_type ";" : aiur_signature_member
syntax (name := moduleParameter) ident ":" ident : aiur_module_parameter
syntax (name := signatureDecl) &"signature" ident "{" aiur_signature_member* "}" : aiur_root_decl
syntax (name := ordinaryMember) aiur_decl : aiur_module_member
syntax (name := opaqueAliasMember) &"opaque" aiur_alias : aiur_module_member
syntax (name := opaqueStructMember) &"opaque" aiur_struct : aiur_module_member
syntax (name := opaqueEnumMember) &"opaque" aiur_enum : aiur_module_member
syntax (name := moduleDecl) &"module" ident
  ("<" sepBy1(aiur_module_parameter, ",", ",", allowTrailingSep) closeAngle)? (":" ident)?
  "{" aiur_module_member* "}" : aiur_root_decl
syntax (name := moduleAlias) &"module" ident
  ("<" sepBy1(aiur_module_parameter, ",", ",", allowTrailingSep) closeAngle)? (":" ident)?
  "=" aiur_module_ref ";" : aiur_root_decl
syntax (name := modules) aiur_root_decl* : aiur_modules

partial def readRef (s : Syntax) : Except String Ref := do
  if s.getKind == ``refApply then
    return .mk (← readName s[0]) (← s[2].getSepArgs.toList.mapM readRef)
  else return .mk (← readName s[0]) []

private def pathParts (s : Syntax) : Except String (List String) := do
  let offset := if s.getKind == ``rootedQualified then 1 else 0
  let head ← readRef s[offset]
  return head.symbol :: (← s[2 + offset].getSepArgs.toList.mapM readName)

private def node (kind : Name) (args : Array Syntax) := Syntax.node .none kind args
private def atom (text : String) := Syntax.atom .none text
private def identifier (text : String) : Syntax := mkIdent (Name.mkSimple text)

/-- A syntax rewrite's state: the results for nodes already rewritten. -/
private abbrev SharedM := StateT (Std.HashMap USize Syntax) (Except String)

/-- `shared`, memoized by node address. The parser's category cache shares the
subtrees that ambiguous alternatives have in common, so a tree with nested
`choice` nodes is a DAG, and visiting it as a tree takes time exponential in
their nesting: braced match arms and nested constructor calls nest deeply.
Every node stays alive while the tree is, so addresses identify nodes. -/
private unsafe def sharedGo (step : (Syntax → SharedM Syntax) → Syntax → SharedM Syntax)
    (s : Syntax) : SharedM Syntax := do
  let key := ptrAddrUnsafe s
  if let some result := (← get)[key]? then return result
  let result ← step (sharedGo step) s
  modify (·.insert key result)
  return result

private unsafe def sharedImpl (step : (Syntax → SharedM Syntax) → Syntax → SharedM Syntax)
    (s : Syntax) : Except String Syntax :=
  (sharedGo step s).run' {}

/-- Rewrite `s` with `step`, which receives the rewrite of the nodes it recurs
on: the least fixed point of `step`. The rewrite of a node depends on the node
alone, so it is computed once for each node that several alternatives share. -/
@[implemented_by sharedImpl]
private opaque shared (step : (Syntax → SharedM Syntax) → Syntax → SharedM Syntax)
    (s : Syntax) : Except String Syntax

/-- Normalize only qualified identifier syntax, then reuse the native expression
reader. No expression is lowered or evaluated by module parsing. -/
private def normalizeStep (moduleNames localTypes : List String) (recur : Syntax → SharedM Syntax)
    (s : Syntax) : SharedM Syntax := do
  let k := s.getKind
  if k == `choice then
    -- Prefer the modular parse of a qualified identifier when both grammars fit.
    let candidates := s.getArgs.toList
    let localConstructor := candidates.find? fun c =>
      [``genericConstructor, ``genericConstructorArgs, ``genericConstructorPattern,
        ``genericConstructorPatternArgs].contains c.getKind &&
        localTypes.contains (c[0].getId.toString) &&
        !(moduleNames.contains (c[0].getId.toString))
    if let some chosen := localConstructor then return ← recur chosen
    let chosen := candidates.find? fun c => [``qualifiedValue, ``qualifiedCall, ``qualifiedPattern,
      ``qualifiedPatternArgs, ``qualifiedGenericCall, ``qualifiedType].contains c.getKind
    if let some chosen := chosen then return ← recur chosen
    return node k (← s.getArgs.mapM recur)
  let s ← match s with
    | .node info kind args => do pure (Syntax.node info kind (← args.mapM recur))
    | s => pure s
  if k == ``rootedCall || k == ``rootedGenericCall then
    return node (if k == ``rootedCall then ``call else ``genericCall)
      (#[identifier ("::" ++ (← readName s[1]))] ++ (s.getArgs.toList.drop 2).toArray)
  if k == ``rootedType then return node ``namedType #[identifier (← readName s[1])]
  if k == ``qualifiedType || k == ``qualifiedAppliedType then
    let name := String.intercalate "::" (← pathParts s[0])
    if k == ``qualifiedType then return node ``namedType #[identifier name]
    return node ``appliedType #[identifier name, s[1], s[2], s[3]]
  if [``qualifiedRecord, ``qualifiedGenericRecord, ``qualifiedRecordPattern, ``qualifiedGenericRecordPattern,
      ``qualifiedGenericConstructor, ``qualifiedGenericConstructorArgs, ``qualifiedGenericPattern, ``qualifiedGenericPatternArgs,
      ``qualifiedGenericCall].contains k then
    let name := String.intercalate "::" (← pathParts s[0])
    let kind := if k == ``qualifiedRecord then ``recordExpr
      else if k == ``qualifiedGenericRecord then ``genericRecordExpr
      else if k == ``qualifiedRecordPattern then ``recordPattern
      else if k == ``qualifiedGenericRecordPattern then ``genericRecordPattern
      else if k == ``qualifiedGenericConstructor then ``genericConstructor
      else if k == ``qualifiedGenericConstructorArgs then ``genericConstructorArgs
      else if k == ``qualifiedGenericPattern then ``genericConstructorPattern
      else if k == ``qualifiedGenericPatternArgs then ``genericConstructorPatternArgs
      else ``genericCall
    return node kind (s.getArgs.set! 0 (identifier name))
  if [``qualifiedValue, ``qualifiedCall, ``qualifiedPattern, ``qualifiedPatternArgs].contains k then
    let parts ← pathParts s[0]
    let first := (← parseRef 128 parts.head!).name
    -- An unknown qualifier may be supplied by a separately parsed fragment.
    -- Only types declared in this module can start local constructor paths.
    let isModule := moduleNames.contains first || !localTypes.contains first
    let constructor := parts.length > (if isModule then 2 else 1)
    let inPattern := k == ``qualifiedPattern || k == ``qualifiedPatternArgs
    let hasArgs := k == ``qualifiedCall || k == ``qualifiedPatternArgs
    if constructor then
      let name := String.intercalate "::" (parts.dropLast)
      let ctor := parts.getLast!
      let kind := if inPattern then (if hasArgs then ``constructorPatternArgs else ``constructorPattern)
        else (if hasArgs then ``constructorCall else ``constructorExpr)
      let args := #[identifier name, atom "::", identifier ctor]
      return node kind (if hasArgs then args ++ #[s[1],s[2],s[3]] else args)
    let name := String.intercalate "::" parts
    if inPattern && hasArgs then throw "a const pattern does not take arguments"
    if hasArgs then return node ``call #[identifier name,s[1],s[2],s[3]]
    return node (if inPattern then ``globalPattern else ``globalExpr) #[atom "::",identifier name]
  if [``constructorExpr, ``constructorCall, ``constructorPattern, ``constructorPatternArgs].contains k then
    let head ← readName s[0]
    if moduleNames.contains head || !localTypes.contains head then
      let full := head ++ "::" ++ (← readName s[2])
      if k == ``constructorCall then return node ``call #[identifier full,s[3],s[4],s[5]]
      if k == ``constructorPatternArgs then throw "a const pattern does not take arguments"
      return node (if k == ``constructorPattern then ``globalPattern else ``globalExpr) #[atom "::",identifier full]
  if k == ``qualifiedMap then
    let nameOf := fun x => do
      if x.getKind == ``globalName then readName x[0]
      else return String.intercalate "::" (← pathParts x[0])
    return node ``mapDefinition ((s.getArgs.set! 8 (identifier (← nameOf s[8]))).set! 10 (identifier (← nameOf s[10])))
  return s

@[inherit_doc normalizeStep]
def normalize (moduleNames localTypes : List String) (s : Syntax) : Except String Syntax :=
  shared (normalizeStep moduleNames localTypes) s

def readDefinitions (ds : List Syntax) : Except String (Definitions Nat) := do
  let enums ← (ds.filter (·.getKind == ``enumDecl)).mapM (fun d => lowerEnum d[0])
  let structs ← (ds.filter (·.getKind == ``structDecl)).mapM (fun d => lowerStruct d[0])
  let aliases ← (ds.filter (·.getKind == ``aliasDecl)).mapM (fun d => lowerAlias d[0])
  let constEntries ← (ds.filter (·.getKind == ``constDecl)).mapM fun d => do
    let s := d[0]
    let typed := s.getKind == ``typedConst
    let annotation ← if typed then some <$> type [] s[3] else pure none
    let decl : Generic.ConstDecl Nat := { name := ← readName s[1], value := ← Generic.Consts.ofExpr (← expr [] s[if typed then 5 else 3]) }
    return (decl,annotation)
  let consts := constEntries.map Prod.fst
  let constTypes := constEntries.filterMap fun (d,t) => t.map (d.name, ·)
  let functions ← (ds.filter (·.getKind == ``functionDecl)).mapM (fun d => lowerFunction [] [] [] d[0] false)
  let parameterPatterns ← (ds.filter (·.getKind == ``functionDecl)).mapM fun d => do
    let s := if d[0].getKind == `choice then d[0][0] else d[0]
    let s := if s.getKind == ``inlineFunction then nativeChoice s[1] else s
    let generic := s.getKind == ``genericFunction
    let params ← if generic then s[3].getSepArgs.toList.mapM readName else pure []
    return (← readName s[1], ← s[if generic then 6 else 3].getSepArgs.toList.mapM fun p => pattern params p[0])
  let tables ← (ds.filter (·.getKind == ``tableDecl)).mapM fun d => do
    let s := d[0]
    return { name := ← readName s[1], rowType := ← type [] s[3], rows := ← s[5].getSepArgs.toList.mapM (expr []) : Generic.Table Nat }
  let maps ← (ds.filter (·.getKind == ``mapDecl)).mapM fun d => do
    let s := nativeChoice d[0]
    let params ← s[3].getSepArgs.toList.mapM fun p => do
      let .bind n ← pattern [] p[0] | throw "map parameters must be named bindings"
      return (n, ← type [] p[2])
    return { name := ← readName s[1], params, result := ← type [] s[6], input := ← readName s[8], output := ← readName s[10] : Generic.MapDecl }
  return ⟨{functions,enums,structs,aliases,consts,tables,maps}, constTypes, parameterPatterns, []⟩

def readSignature (s : Syntax) : Except String Signature := do
  let mut result : Signature := {name := ← readName s[1]}
  for m in s[3].getArgs do
    let k := m.getKind
    if [``sigAbstract, ``sigGenericAbstract, ``sigOpaqueAbstract, ``sigGenericOpaqueAbstract].contains k then
      let isOpaque := k == ``sigOpaqueAbstract || k == ``sigGenericOpaqueAbstract
      let offset := if isOpaque then 1 else 0
      let generic := k == ``sigGenericAbstract || k == ``sigGenericOpaqueAbstract
      let params ← if generic then m[3 + offset].getSepArgs.toList.mapM readName else pure []
      result := {result with types := result.types ++ [⟨← readName m[1 + offset],params,none,isOpaque⟩]}
    else if k == ``sigAlias then
      let d ← lowerAlias m[0]
      result := {result with types := result.types ++ [⟨d.name,d.typeParams,some d.target,false⟩]}
    else if k == ``sigConst then
      result := {result with consts := result.consts ++ [(← readName m[1], ← type [] m[3])]}
    else if k == ``sigTable then
      result := {result with tables := result.tables ++ [(← readName m[1], ← type [] m[3])]}
    else
      let generic := k == ``sigGenericFunction
      let ps ← if generic then m[3].getSepArgs.toList.mapM readName else pure []
      let offset := if generic then 3 else 0
      let params ← m[3+offset].getSepArgs.toList.mapM fun param => do
        let .bind name ← pattern ps param[0] | throw "signature parameters must be named bindings"
        return (name, ← type ps param[2])
      result := {result with functions := result.functions ++
        [⟨← readName m[1],ps,params,← type ps m[6+offset]⟩]}
  return result

private def checkIdentifiersStep (recur : Syntax → SharedM Syntax) (s : Syntax) : SharedM Syntax := do
  if s.isIdent then
    let n ← readName s
    unless simpleIdentifier n || n == "Field" do throw s!"invalid source identifier '{n}'"
  else discard <| s.getArgs.mapM recur
  return s

/-- A module-only root; source files and imports are not part of this frontend. -/
private def checkIdentifiers (s : Syntax) : Except String Unit :=
  discard <| shared checkIdentifiersStep s

private def dottedParts (s : Syntax) : List String :=
  s.getId.components.map fun | .str _ n => n | n => n.toString

private def splitDottedStep (recur : Syntax → SharedM Syntax) (s : Syntax) : SharedM Syntax := do
  let .node info k args := s | return s
  let s := Syntax.node info k (← args.mapM recur)
  let members (base : Syntax) (fields : List String) :=
    fields.foldl (fun e f => node ``memberExpr #[e, atom ".", identifier f]) base
  if k == ``variableExpr then
    if let head :: fields@(_ :: _) := dottedParts s[0] then
      return members (node ``variableExpr #[identifier head]) fields
  else if k == ``memberExpr then
    if let first :: fields@(_ :: _) := dottedParts s[2] then
      return members (node ``memberExpr #[s[0], s[1], identifier first]) fields
  else if k == ``updateEntry then
    let steps := s[0].getArgs.flatMap fun step =>
      if step.getKind == ``updateMember then
        (dottedParts step[1]).toArray.map fun f => node ``updateMember #[atom ".", identifier f]
      else #[step]
    return s.setArg 0 (node nullKind steps)
  return s

/-- Lean's tokenizer reads `a.b` as one dotted identifier, and `.a.b` as `.`
followed by one. The string frontend separates every `.` before parsing, so it
reads member accesses instead; rebuild those. Any other dotted identifier is
left to `checkIdentifiers`, which rejects it. -/
def splitDotted (s : Syntax) : Except String Syntax := shared splitDottedStep s

/-- Lower parsed root declarations to a module program. The string frontend and
embedded `aiur⟦ … ⟧` blocks share it, so both produce the same program. -/
def ofDecls (ds : List Syntax) : Except String (Program Nat) := do
  let ds ← ds.mapM splitDotted
  ds.forM checkIdentifiers
  let names ← (ds.filter (·.getKind != ``signatureDecl)).mapM fun d => readName d[1]
  let mut result : Program Nat := {}
  for s in ds do
    if s.getKind == ``signatureDecl then
      result := {result with signatures := result.signatures ++ [← readSignature (← normalize names [] s)]}
    else
      let parameters ← if s[2].getArgs.isEmpty then pure [] else
        s[2][1].getSepArgs.toList.mapM fun p => return (← readName p[0], ← readName p[2])
      let signature ← if s[3].getArgs.isEmpty then pure none else some <$> readName s[3][1]
      let body ← if s.getKind == ``moduleAlias then Body.alias <$> readRef s[5] else do
        let members := s[5].getArgs.toList.map nativeChoice
        let opaqueTypes ← (members.filter (·.getKind != ``ordinaryMember)).mapM
          (fun m => readName (nativeChoice m[1])[1])
        let ds := members.map fun m =>
          if m.getKind == ``ordinaryMember then m[0]
          else node (if m.getKind == ``opaqueAliasMember then ``aliasDecl
            else if m.getKind == ``opaqueStructMember then ``structDecl else ``enumDecl) #[m[1]]
        let localTypes ← (ds.filter fun d => [``enumDecl, ``structDecl, ``aliasDecl].contains d.getKind).mapM
          (fun d => readName (nativeChoice d[0])[1])
        let ds ← ds.mapM (normalize (names ++ parameters.map Prod.fst) localTypes)
        pure (Body.definitions { (← readDefinitions ds) with opaqueTypes })
      result := {result with modules := result.modules ++ [⟨← readName s[1],parameters,signature,body⟩]}
  return result

def parse (env : Lean.Environment) (source : String) : Except String (Program Nat) := do
  let s ← Parser.runParserCategory env `aiur_modules (← prepareSource source) "<aiur modules>"
  ofDecls s[0].getArgs.toList

def ofString (env : Lean.Environment) (source : String) : Except String (Program Nat) := do
  let p ← parse env source
  checkTemplates p
  return p

@[term_elab Aiur.Frontend.aiurTerm]
def elabModules : TermElab := fun stx expected => do
  let some expected := expected | throwUnsupportedSyntax
  unless (← Meta.whnf expected).isAppOf ``Program do throwUnsupportedSyntax
  match ofString (← getEnv) (stx[1].isStrLit?.getD "") with
  | .error e => throwErrorAt stx[1] "{e}"
  | .ok p => return Lean.toExpr p

elab "aiur_modules% " source:str : term => do
  match ofString (← getEnv) source.getString with
  | .error e => throwErrorAt source "{e}"
  | .ok p => return Lean.toExpr p

/-- Parse module declarations with the categories above, and keep only their
source text, as one atom.

Ambiguous alternatives share the subtrees they have in common, so the parse
of a block is a DAG of `choice` nodes. Linters walk a command's syntax as a
tree, which takes time exponential in the nesting of those alternatives
(minutes for a generated module). The parse checks the block where Lean reads
it, with errors at their positions; the elaborator parses the text again. -/
def declsTextFn : Lean.Parser.ParserFn := fun c s =>
  let iniSz := s.stackSize
  let startPos := s.pos
  let s := (Lean.Parser.many (Lean.Parser.categoryParser `aiur_root_decl 0)).fn c s
  if s.hasError then s else
  let stopPos := s.pos
  let info := SourceInfo.original (c.mkEmptySubstringAt startPos) startPos
    (c.mkEmptySubstringAt stopPos) stopPos
  (s.shrinkStack iniSz).pushSyntax (Syntax.atom info (c.extract startPos stopPos))

@[inherit_doc declsTextFn]
def declsText : Lean.Parser.Parser where
  «fn» := declsTextFn  -- `fn` is an Aiur keyword here
  info := (Lean.Parser.many (Lean.Parser.categoryParser `aiur_root_decl 0)).info

@[combinator_formatter declsText]
def declsText.formatter : PrettyPrinter.Formatter := PrettyPrinter.Formatter.visitAtom Name.anonymous

@[combinator_parenthesizer declsText]
def declsText.parenthesizer : PrettyPrinter.Parenthesizer := PrettyPrinter.Parenthesizer.visitToken

/-- Module declarations written as Lean syntax:
`def m : Aiur.Modules.Program Nat := aiur⟦ module M { … } ⟧`.

Lean parses the block, with the categories above, when it parses the file, so
a syntax error is reported where it is. The elaborator lowers the block's text
exactly as the string frontend lowers source text after its lexical
preparation (`declsText` says why it does not keep the parse). Only the
lexical surface differs from source text:
- comments are Lean comments;
- a block label is written `@name`, which source text spells `'name`;
- a negated operand keeps its space, as in `a - -b` and `a / -b`, since a
  doubled dash, or a slash and a dash, opens a comment;
- a member of a projection needs parentheses, as in `(p.0).f`: Lean reads
  `0.f` as a malformed decimal literal.

Nested generic arguments close as in Rust (`List<List<Field>>`; `closeAngle`)
and indices chain (`p.1.0`), in both forms.

The result is not template-checked: a fragment may use modules defined in
other fragments. Check the composed program with `Modules.checkTemplates`
(`#aiur_check`), as `Modules.prepare` also does. -/
syntax (name := embedded) "aiur⟦" declsText "⟧" : term

/-- Run `x` without counting its allocations against `maxHeartbeats`, which
bounds elaboration's search. Lowering a program block and evaluating a program
are linear in its size, so a large program needs no heartbeat budget. -/
private def uncounted [Monad m] [MonadLiftT BaseIO m] (x : m α) : m α := do
  let heartbeats ← IO.getNumHeartbeats
  let result ← x
  IO.setNumHeartbeats heartbeats
  return result

/-- Lower the text of an `aiur⟦ … ⟧` block. `aiur_embed` uses it as well. -/
def ofBlockText (env : Lean.Environment) (text : String) : Except String (Program Nat) := do
  let s ← Parser.runParserCategory env `aiur_modules text "<aiur⟦ … ⟧>"
  ofDecls s[0].getArgs.toList

@[term_elab embedded]
def elabEmbedded : TermElab := fun stx _ => uncounted do
  match ofBlockText (← getEnv) stx[1].getAtomVal with
  | .error e => throwErrorAt stx "{e}"
  | .ok p => return Lean.toExpr p

/-- Fail elaboration, with the checker's message, unless the module program
`p` passes `Modules.checkTemplates`. Composed embedded fragments are checked
this way where they are assembled. -/
elab "#aiur_check " p:term : command => Lean.Elab.Command.liftTermElabM do
  let type := mkApp2 (mkConst ``Except [0, 0]) (mkConst ``String) (mkConst ``Unit)
  let result ← unsafe evalTerm (Except String Unit) type (← `(Aiur.Modules.checkTemplates $p))
  if let .error e := result then throwErrorAt p "{e}"

/-- `aiur_eval% e`, for `e : String`, is the string literal `e` evaluates to
when the file is compiled. Applications use it to record a program's digest as
a constant. -/
elab "aiur_eval% " e:term : term => do
  return mkStrLit (← uncounted (unsafe evalTerm String (mkConst ``String) e))

end Aiur.Modules.Frontend
