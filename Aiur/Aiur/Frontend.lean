import Aiur.Typecheck
import Lean

namespace Aiur.Frontend

open Lean Elab Term

declare_syntax_cat aiur_type
declare_syntax_cat aiur_expr
declare_syntax_cat aiur_pattern
declare_syntax_cat aiur_arm
declare_syntax_cat aiur_param
declare_syntax_cat aiur_function
declare_syntax_cat aiur_constructor
declare_syntax_cat aiur_enum
-- Declaration keywords need not reserve ordinary identifiers in surrounding Lean code.
declare_syntax_cat aiur_table (behavior := symbol)
declare_syntax_cat aiur_map (behavior := symbol)
declare_syntax_cat aiur_decl (behavior := symbol)
declare_syntax_cat aiur_program (behavior := symbol)

syntax:75 (name := pointerType) "&" aiur_type:75 : aiur_type
syntax (name := namedType) ident : aiur_type
syntax (name := unitType) "(" ")" : aiur_type
syntax (name := typeParens) "(" aiur_type ")" : aiur_type
syntax (name := tupleType) "(" aiur_type "," sepBy(aiur_type, ",", ",", allowTrailingSep) ")" : aiur_type
syntax (name := unitExpr) "(" ")" : aiur_expr
syntax (name := tupleExpr) "(" aiur_expr "," sepBy(aiur_expr, ",", ",", allowTrailingSep) ")" : aiur_expr
syntax:80 (name := project) aiur_expr:80 "." num : aiur_expr
syntax (name := letValue) "let" aiur_pattern "=" aiur_expr ";" aiur_expr : aiur_expr
syntax (name := literal) num : aiur_expr
syntax (name := variableExpr) ident : aiur_expr
syntax (name := constructorExpr) ident "::" ident : aiur_expr
syntax (name := constructorCall) ident "::" ident "(" sepBy(aiur_expr, ",", ",", allowTrailingSep) ")" : aiur_expr
syntax (name := parens) "(" aiur_expr ")" : aiur_expr
syntax (name := block) "{" aiur_expr "}" : aiur_expr
syntax (name := call) ident "(" sepBy(aiur_expr, ",", ",", allowTrailingSep) ")" : aiur_expr
syntax (name := hintExpr) ident "::<" aiur_type ">" "(" aiur_expr ")" : aiur_expr
syntax (name := channelHintExpr) ident "::<" aiur_type ">" "(" str "," aiur_expr ")" : aiur_expr
syntax:75 (name := store) "&" aiur_expr:75 : aiur_expr
syntax:75 (name := load) "*" aiur_expr:75 : aiur_expr
syntax:75 (name := neg) "-" aiur_expr:75 : aiur_expr
syntax:70 (name := mul) aiur_expr:70 "*" aiur_expr:71 : aiur_expr
syntax:70 (name := div) aiur_expr:70 "/" aiur_expr:71 : aiur_expr
syntax:65 (name := add) aiur_expr:65 "+" aiur_expr:66 : aiur_expr
syntax:65 (name := sub) aiur_expr:65 "-" aiur_expr:66 : aiur_expr
syntax (name := literalPattern) num : aiur_pattern
syntax (name := wildcardPattern) "_" : aiur_pattern
syntax (name := bindPattern) ident : aiur_pattern
syntax (name := constructorPattern) ident "::" ident : aiur_pattern
syntax (name := constructorPatternArgs) ident "::" ident "(" sepBy(aiur_pattern, ",", ",", allowTrailingSep) ")" : aiur_pattern
syntax (name := unitPattern) "(" ")" : aiur_pattern
syntax (name := patternParens) "(" aiur_pattern ")" : aiur_pattern
syntax (name := tuplePattern) "(" aiur_pattern "," sepBy(aiur_pattern, ",", ",", allowTrailingSep) ")" : aiur_pattern
syntax (name := arm) aiur_pattern "=>" aiur_expr : aiur_arm
syntax (name := matchValue) "match" aiur_expr "{"
  sepBy1(aiur_arm, ",", ",", allowTrailingSep) "}" : aiur_expr
syntax (name := param) aiur_pattern ":" aiur_type : aiur_param
syntax (name := function) "fn" ident "(" sepBy(aiur_param, ",", ",", allowTrailingSep) ")"
  "->" aiur_type "{" aiur_expr "}" : aiur_function
syntax (name := nullaryConstructor) ident : aiur_constructor
syntax (name := payloadConstructor) ident "(" sepBy(aiur_type, ",", ",", allowTrailingSep) ")" : aiur_constructor
syntax (name := enumDefinition) "enum" ident "{" sepBy(aiur_constructor, ",", ",", allowTrailingSep) "}" : aiur_enum
syntax (name := tableDefinition) &"table" ident ":" aiur_type "{"
  sepBy(aiur_expr, ",", ",", allowTrailingSep) "}" : aiur_table
syntax (name := mapDefinition) &"map" ident "(" sepBy(aiur_param, ",", ",", allowTrailingSep) ")"
  "->" aiur_type "=" ident "=>" ident ";" : aiur_map
syntax (name := tableDecl) aiur_table : aiur_decl
syntax (name := mapDecl) aiur_map : aiur_decl
syntax (name := functionDecl) aiur_function : aiur_decl
syntax (name := enumDecl) aiur_enum : aiur_decl
syntax (name := program) aiur_decl* : aiur_program

private def readName (stx : Syntax) : Except String String :=
  match stx.getId with
  | .str .anonymous name => .ok name
  | _ => .error "expected a simple function or parameter name"

private partial def lowerType (stx : Syntax) : Except String Ty := do
  if stx.getKind == ``pointerType then return .ptr (← lowerType stx[1])
  else if stx.getKind == ``namedType then
    if stx[0].getId == `Field then return .field
    else return .enum (← readName stx[0])
  else if stx.getKind == ``unitType then return .tuple []
  else if stx.getKind == ``typeParens then lowerType stx[1]
  else if stx.getKind == ``tupleType then
    return .tuple ((← lowerType stx[1]) :: (← stx[3].getSepArgs.toList.mapM lowerType))
  else throw "expected a field, tuple, pointer, or enum type"

private partial def lowerPattern (stx : Syntax) : Except String (Pattern Nat) := do
  if stx.getKind == `choice then
    let mut error := "unsupported ambiguous pattern"
    for alternative in stx.getArgs do
      match lowerPattern alternative with
      | .ok pattern => return pattern
      | .error message => error := message
    throw error
  else if stx.getKind == ``literalPattern then
    let some value := stx[0].isNatLit? | throw "expected a natural-number pattern"
    return .literal value
  else if stx.getKind == ``wildcardPattern then return .wildcard
  else if stx.getKind == ``bindPattern then return .bind (← readName stx[0])
  else if stx.getKind == ``constructorPattern then
    return .construct (← readName stx[0]) (← readName stx[2]) []
  else if stx.getKind == ``constructorPatternArgs then
    return .construct (← readName stx[0]) (← readName stx[2])
      (← stx[4].getSepArgs.toList.mapM lowerPattern)
  else if stx.getKind == ``unitPattern then return .tuple []
  else if stx.getKind == ``patternParens then lowerPattern stx[1]
  else if stx.getKind == ``tuplePattern then
    return .tuple ((← lowerPattern stx[1]) :: (← stx[3].getSepArgs.toList.mapM lowerPattern))
  else throw "expected a literal, wildcard, binding, or tuple pattern"

/-- Lower Lean's syntax tree for the embedded language; no field is chosen here. -/
private partial def lowerExpr (stx : Syntax) : Except String (Aiur.Expr Nat) := do
  let kind := stx.getKind
  if kind == `choice then
    let mut error := "unsupported ambiguous expression"
    for alternative in stx.getArgs do
      match lowerExpr alternative with
      | .ok expr => return expr
      | .error message => error := message
    throw error
  else if kind == ``literal then
    let some value := stx[0].isNatLit? | throw "expected a natural-number literal"
    return .literal value
  else if kind == ``constructorExpr then
    return .construct (← readName stx[0]) (← readName stx[2]) []
  else if kind == ``constructorCall then
    return .construct (← readName stx[0]) (← readName stx[2])
      (← stx[4].getSepArgs.toList.mapM lowerExpr)
  else if kind == ``unitExpr then return .tuple []
  else if kind == ``tupleExpr then
    return .tuple ((← lowerExpr stx[1]) :: (← stx[3].getSepArgs.toList.mapM lowerExpr))
  else if kind == ``project then
    let some index := stx[2].isNatLit? | throw "expected a tuple index"
    return .project (← lowerExpr stx[0]) index
  else if kind == ``letValue then
    return .letValue (← lowerPattern stx[1]) (← lowerExpr stx[3]) (← lowerExpr stx[5])
  else if kind == ``variableExpr then
    return .var (← readName stx[0])
  else if kind == ``parens || kind == ``block then
    lowerExpr stx[1]
  else if kind == ``store then return .store (← lowerExpr stx[1])
  else if kind == ``load then return .load (← lowerExpr stx[1])
  else if kind == ``channelHintExpr then
    if (← readName stx[0]) != "hint" then throw "only hint supports a channel"
    return .hint (← lowerType stx[2]) (← lowerExpr stx[7]) (stx[5].isStrLit?.getD "")
  else if kind == ``hintExpr then
    if (← readName stx[0]) != "hint" then throw "only hint supports an explicit result type"
    return .hint (← lowerType stx[2]) (← lowerExpr stx[5])
  else if kind == ``neg then
    return .neg (← lowerExpr stx[1])
  else if kind == ``add || kind == ``sub || kind == ``mul || kind == ``div then
    let op := if kind == ``add then BinOp.add else if kind == ``sub then .sub
      else if kind == ``mul then .mul else .div
    return .binary op (← lowerExpr stx[0]) (← lowerExpr stx[2])
  else if kind == ``call then
    return .call (← readName stx[0]) (← stx[2].getSepArgs.toList.mapM lowerExpr)
  else if kind == ``matchValue then
    let scrutinee ← lowerExpr stx[1]
    let arms ← stx[3].getSepArgs.toList.mapM fun arm => do
      return (← lowerPattern arm[0], ← lowerExpr arm[2])
    return .matchValue scrutinee arms
  else
    throw s!"unsupported expression syntax: {kind}"

private def lowerEnum (stx : Syntax) : Except String EnumDecl := do
  let name ← readName stx[1]
  let constructors ← stx[3].getSepArgs.toList.mapM fun ctor => do
    let fields ← if ctor.getKind == ``payloadConstructor then
      ctor[2].getSepArgs.toList.mapM lowerType
      else pure []
    return { name := ← readName ctor[0], fields : ConstructorDecl }
  return { name, constructors }

private partial def lowerFunction (decls : Declarations) (stx : Syntax) : Except String (Aiur.Function Nat) := do
  if stx.getKind == `choice then
    let mut error := "unsupported ambiguous function"
    for alternative in stx.getArgs do
      match lowerFunction decls alternative with
      | .ok definition => return definition
      | .error message => error := message
    throw error
  let name ← readName stx[1]
  let mut params := []
  let mut destructuring := []
  let mut names := []
  for (param, index) in stx[3].getSepArgs.toList.zipIdx do
    let pattern ← lowerPattern param[0]
    let type ← lowerType param[2]
    if !pattern.irrefutable decls then throw s!"parameter patterns must be irrefutable in function '{name}'"
    let bindings ← (checkPattern decls name pattern type).mapError toString
    names := names ++ bindings.map Prod.fst
    match pattern with
    | .bind key => params := params ++ [(key, type)]
    | _ =>
        let key := s!"$arg{index}"
        params := params ++ [(key, type)]
        destructuring := destructuring ++ [(pattern, key)]
  if let some duplicate := findDuplicate names [] then
    throw s!"duplicate parameter '{duplicate}' in function '{name}'"
  let body ← lowerExpr stx[8]
  return {
    name, params
    result := ← lowerType stx[6]
    body := destructuring.foldr (fun (pattern, key) body => .letValue pattern (.var key) body) body
  }

private def constantOfExpr : Aiur.Expr Nat → Except String (Constant Nat)
  | .literal value => pure (.field value)
  | .tuple items => (.tuple ·) <$> items.mapM constantOfExpr
  | .construct name ctor args => (.construct name ctor ·) <$> args.mapM constantOfExpr
  | _ => throw "table rows must be constant literals, tuples, or enum constructors; pointers are forbidden"
termination_by expr => sizeOf expr

private def lowerTable (stx : Syntax) : Except String (Table Nat) := do
  return {
    name := ← readName stx[1]
    rowType := ← lowerType stx[3]
    rows := ← stx[5].getSepArgs.toList.mapM fun row => do constantOfExpr (← lowerExpr row)
  }

private partial def lowerMap (stx : Syntax) : Except String MapDecl := do
  if stx.getKind == `choice then
    let mut error := "unsupported ambiguous map"
    for alternative in stx.getArgs do
      match lowerMap alternative with
      | .ok decl => return decl
      | .error message => error := message
    throw error
  let params ← stx[3].getSepArgs.toList.mapM fun param => do
    let .bind name ← lowerPattern param[0] | throw "map parameters must be named bindings"
    return (name, ← lowerType param[2])
  return {
    name := ← readName stx[1]
    params
    result := ← lowerType stx[6]
    input := ← readName stx[8]
    output := ← readName stx[10]
  }

/-- Mask Rust comments before invoking Lean's parser, preserving lines and token boundaries. -/
def maskComments : List Char → Nat → Bool → Except String (List Char)
  | [], depth, _ =>
      if depth == 0 then .ok [] else .error "unterminated block comment"
  | '/' :: '/' :: rest, 0, false => do
      return ' ' :: ' ' :: (← maskComments rest 0 true)
  | '/' :: '*' :: rest, depth, false => do
      return ' ' :: ' ' :: (← maskComments rest (depth + 1) false)
  | '*' :: '/' :: rest, depth + 1, false => do
      return ' ' :: ' ' :: (← maskComments rest depth false)
  | char :: rest, depth, inLine => do
      let masked := if (inLine || depth > 0) && char != '\n' && char != '\r' then ' ' else char
      return masked :: (← maskComments rest depth (inLine && char != '\n'))

/-- Keep adjacent arithmetic operators from being interpreted as Lean comments. -/
def normalizeWhitespace : List Char → List Char
  | [] => []
  | '.' :: '.' :: '=' :: rest => ' ' :: '.' :: '.' :: '=' :: ' ' :: normalizeWhitespace rest
  | '.' :: '.' :: rest => ' ' :: '.' :: '.' :: ' ' :: normalizeWhitespace rest
  | char :: rest =>
      let normalized := if char == '\t' || char == '\r' then ' ' else char
      -- Keep chained tuple indices such as `p.1.0` from becoming a decimal token.
      if char == '&' || char == '*' then normalized :: ' ' :: normalizeWhitespace rest
      else if char == '.' then ' ' :: '.' :: ' ' :: normalizeWhitespace rest
      else if (char == '-' || char == '/') && rest.head? == some '-' then
        normalized :: ' ' :: normalizeWhitespace rest
      else
        normalized :: normalizeWhitespace rest

/-- Parse and typecheck a string using the syntax categories registered in Lean. -/
def ofString (env : Environment) (source : String) : Except String (Program Nat) := do
  let source := String.ofList (normalizeWhitespace (← maskComments source.toList 0 false))
  let stx ← Parser.runParserCategory env `aiur_program source "<aiur>"
  let declarations := stx[0].getArgs.toList
  for d in declarations do
    unless [``enumDecl, ``functionDecl, ``tableDecl, ``mapDecl].contains d.getKind do
      throw "declaration requires the generic source frontend (Generic.Program Nat)"
  let enums ← (declarations.filter (·.getKind == ``enumDecl)).mapM (fun d => lowerEnum d[0])
  (checkDeclarations enums).mapError toString
  let program := {
    functions := ← (declarations.filter (·.getKind == ``functionDecl)).mapM (fun d => lowerFunction enums d[0])
    enums
    tables := ← (declarations.filter (·.getKind == ``tableDecl)).mapM (fun d => lowerTable d[0])
    maps := ← (declarations.filter (·.getKind == ``mapDecl)).mapM (fun d => lowerMap d[0])
  }
  match typecheck program with
  | .error error => throw (toString error)
  | .ok () => pure program

private def quoteList (type : Lean.Expr) (values : List Lean.Expr) : Lean.Expr :=
  values.foldr (fun value tail => mkApp3 (mkConst ``List.cons [0]) type value tail)
    (mkApp (mkConst ``List.nil [0]) type)

private def natType : Lean.Expr := mkConst ``Nat
private def exprType : Lean.Expr := mkApp (mkConst ``Aiur.Expr) natType
private def patternType : Lean.Expr := mkApp (mkConst ``Pattern) natType

private def quoteOp : BinOp → Lean.Expr
  | .add => mkConst ``BinOp.add
  | .sub => mkConst ``BinOp.sub
  | .mul => mkConst ``BinOp.mul
  | .div => mkConst ``BinOp.div

private def quoteTy : Ty → Lean.Expr
  | .field => mkConst ``Ty.field
  | .enum name => mkApp (mkConst ``Ty.enum) (toExpr name)
  | .ptr target => mkApp (mkConst ``Ty.ptr) (quoteTy target)
  | .tuple items => mkApp (mkConst ``Ty.tuple) (quoteList (mkConst ``Ty) (items.map quoteTy))

private def quotePattern : Pattern Nat → Lean.Expr
  | .literal value => mkApp2 (mkConst ``Pattern.literal) natType (toExpr value)
  | .wildcard => mkApp (mkConst ``Pattern.wildcard) natType
  | .bind name => mkApp2 (mkConst ``Pattern.bind) natType (toExpr name)
  | .tuple items => mkApp2 (mkConst ``Pattern.tuple) natType (quoteList patternType (items.map quotePattern))
  | .construct name ctor args => mkApp4 (mkConst ``Pattern.construct) natType (toExpr name) (toExpr ctor)
      (quoteList patternType (args.map quotePattern))

private def quoteExpr : Aiur.Expr Nat → Lean.Expr
  | .literal value => mkApp2 (mkConst ``Aiur.Expr.literal) natType (toExpr value)
  | .var name => mkApp2 (mkConst ``Aiur.Expr.var) natType (toExpr name)
  | .tuple items => mkApp2 (mkConst ``Aiur.Expr.tuple) natType (quoteList exprType (items.map quoteExpr))
  | .construct name ctor args => mkApp4 (mkConst ``Aiur.Expr.construct) natType (toExpr name) (toExpr ctor)
      (quoteList exprType (args.map quoteExpr))
  | .project value index => mkApp3 (mkConst ``Aiur.Expr.project) natType (quoteExpr value) (toExpr index)
  | .letValue pattern value body =>
      mkApp4 (mkConst ``Aiur.Expr.letValue) natType (quotePattern pattern) (quoteExpr value) (quoteExpr body)
  | .store value => mkApp2 (mkConst ``Aiur.Expr.store) natType (quoteExpr value)
  | .load pointer => mkApp2 (mkConst ``Aiur.Expr.load) natType (quoteExpr pointer)
  | .hint type key channel => mkApp4 (mkConst ``Aiur.Expr.hint) natType (quoteTy type) (quoteExpr key) (toExpr channel)
  | .neg value => mkApp2 (mkConst ``Aiur.Expr.neg) natType (quoteExpr value)
  | .assertEq assertion left right =>
      let metadata := mkApp2 (mkConst ``Aiur.Assertion.mk)
        (toExpr assertion.message) (toExpr assertion.runtimeCheck)
      mkApp4 (mkConst ``Aiur.Expr.assertEq) natType metadata (quoteExpr left) (quoteExpr right)
  | .binary op left right =>
      mkApp4 (mkConst ``Aiur.Expr.binary) natType (quoteOp op) (quoteExpr left) (quoteExpr right)
  | .call name args =>
      mkApp3 (mkConst ``Aiur.Expr.call) natType (toExpr name)
        (quoteList exprType (args.map quoteExpr))
  | .matchValue scrutinee arms =>
      let armType := mkApp2 (mkConst ``Prod [0, 0]) patternType exprType
      let arms := arms.map fun arm =>
        mkApp4 (mkConst ``Prod.mk [0, 0]) patternType exprType
          (quotePattern arm.1) (quoteExpr arm.2)
      mkApp3 (mkConst ``Aiur.Expr.matchValue) natType (quoteExpr scrutinee) (quoteList armType arms)
termination_by expr => sizeOf expr
decreasing_by
  all_goals simp_wf
  all_goals
    first
    | omega
    | have h := List.sizeOf_lt_of_mem ‹_ ∈ _›
      first
      | omega
      | cases arm
        simp_all only [Prod.mk.sizeOf_spec]
        omega

private def quoteFunction (defn : Aiur.Function Nat) : Lean.Expr :=
  let paramType := mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``String) (mkConst ``Ty)
  let params := defn.params.map fun (name, type) =>
    mkApp4 (mkConst ``Prod.mk [0, 0]) (mkConst ``String) (mkConst ``Ty) (toExpr name) (quoteTy type)
  mkApp5 (mkConst ``Aiur.Function.mk) natType (toExpr defn.name) (quoteList paramType params)
    (quoteTy defn.result) (quoteExpr defn.body)

private def quoteEnum (decl : EnumDecl) : Lean.Expr :=
  let constructors := decl.constructors.map fun ctor =>
    mkApp2 (mkConst ``ConstructorDecl.mk) (toExpr ctor.name)
      (quoteList (mkConst ``Ty) (ctor.fields.map quoteTy))
  mkApp2 (mkConst ``EnumDecl.mk) (toExpr decl.name)
    (quoteList (mkConst ``ConstructorDecl) constructors)

private def quoteConstant : Constant Nat → Lean.Expr
  | .field value => mkApp3 (mkConst ``Value.field) natType (mkConst ``Empty) (toExpr value)
  | .tuple items => mkApp3 (mkConst ``Value.tuple) natType (mkConst ``Empty)
      (quoteList (mkApp2 (mkConst ``Value) natType (mkConst ``Empty)) (items.map quoteConstant))
  | .construct name ctor args => mkApp5 (mkConst ``Value.construct) natType (mkConst ``Empty)
      (toExpr name) (toExpr ctor)
      (quoteList (mkApp2 (mkConst ``Value) natType (mkConst ``Empty)) (args.map quoteConstant))
  | .ptr _ address => nomatch address
termination_by value => sizeOf value

private def quoteTable (trace : Table Nat) : Lean.Expr :=
  mkApp4 (mkConst ``Table.mk) natType (toExpr trace.name) (quoteTy trace.rowType)
    (quoteList (mkApp (mkConst ``Constant) natType) (trace.rows.map quoteConstant))

private def quoteMap (definition : MapDecl) : Lean.Expr :=
  let paramType := mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``String) (mkConst ``Ty)
  let params := definition.params.map fun (name, type) =>
    mkApp4 (mkConst ``Prod.mk [0, 0]) (mkConst ``String) (mkConst ``Ty) (toExpr name) (quoteTy type)
  mkApp5 (mkConst ``MapDecl.mk) (toExpr definition.name) (quoteList paramType params)
    (quoteTy definition.result) (toExpr definition.input) (toExpr definition.output)

private def quoteProgram (program : Program Nat) : Lean.Expr :=
  mkApp5 (mkConst ``Program.mk) natType
    (quoteList (mkApp (mkConst ``Aiur.Function) natType) (program.functions.map quoteFunction))
    (quoteList (mkConst ``EnumDecl) (program.enums.map quoteEnum))
    (quoteList (mkApp (mkConst ``Table) natType) (program.tables.map quoteTable))
    (quoteList (mkConst ``MapDecl) (program.maps.map quoteMap))

/-- Elaborate a Rust-like source string directly to a checked `Program Nat`. -/
elab (name := aiurTerm) "aiur% " source:str : term => do
  match ofString (← getEnv) source.getString with
  | .error error => throwErrorAt source "{error}"
  | .ok program => return quoteProgram program

end Aiur.Frontend
