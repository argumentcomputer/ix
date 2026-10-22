import Aiur.Frontend
import Aiur.Generic.Runtime

set_option backward.do.legacy false

namespace Aiur.Generic.Frontend
open Lean Elab Term
open Aiur.Frontend

declare_syntax_cat aiur_body (behavior := symbol)
syntax (name := bodyTail) aiur_expr : aiur_body
syntax (name := bodyEnd) aiur_expr ";" : aiur_body
syntax (name := bodySequence) aiur_expr ";" aiur_body : aiur_body
syntax (name := bodyLetEnd) "let" aiur_pattern "=" aiur_expr ";" : aiur_body
syntax (name := bodyLet) "let" aiur_pattern "=" aiur_expr ";" aiur_body : aiur_body
syntax (name := bodyLetTypedEnd) "let" aiur_pattern ":" aiur_type "=" aiur_expr ";" : aiur_body
syntax (name := bodyLetTyped) "let" aiur_pattern ":" aiur_type "=" aiur_expr ";" aiur_body : aiur_body
syntax (name := ascribeExpr) "(" aiur_expr ":" aiur_type ")" : aiur_expr
syntax (name := assertExpr) "assert_eq!" "(" aiur_expr "," aiur_expr (atomic("," str))? (",")? ")" : aiur_expr
syntax (name := constrainExpr) "constrain_eq!" "(" aiur_expr "," aiur_expr (atomic("," str))? (",")? ")" : aiur_expr
syntax (name := debugExpr) "debug!" "(" str ("," sepBy(aiur_expr, ",", ",", allowTrailingSep))? ")" : aiur_expr
syntax (name := blockStatements) "{" (aiur_body)? "}" : aiur_expr
syntax (name := functionStatements) "fn" ident
  "(" sepBy(aiur_param, ",", ",", allowTrailingSep) ")" "->" aiur_type "{" (aiur_body)? "}" : aiur_function

syntax (name := appliedType) ident "<" sepBy1(aiur_type, ",", ",", allowTrailingSep) ">" : aiur_type
syntax (name := genericFunction) "fn" ident "<" sepBy1(ident, ",", ",", allowTrailingSep) ">"
  "(" sepBy(aiur_param, ",", ",", allowTrailingSep) ")" "->" aiur_type "{" (aiur_body)? "}" : aiur_function
syntax (name := inlineFunction) "inline" aiur_function : aiur_function
syntax (name := genericEnum) "enum" ident "<" sepBy1(ident, ",", ",", allowTrailingSep) ">"
  "{" sepBy(aiur_constructor, ",", ",", allowTrailingSep) "}" : aiur_enum
syntax (name := genericCall) ident "::<" sepBy1(aiur_type, ",", ",", allowTrailingSep) ">"
  "(" sepBy(aiur_expr, ",", ",", allowTrailingSep) ")" : aiur_expr
syntax (name := genericConstructor) ident "::<" sepBy1(aiur_type, ",", ",", allowTrailingSep) ">" "::" ident : aiur_expr
syntax (name := genericConstructorArgs) ident "::<" sepBy1(aiur_type, ",", ",", allowTrailingSep) ">" "::" ident
  "(" sepBy(aiur_expr, ",", ",", allowTrailingSep) ")" : aiur_expr
declare_syntax_cat aiur_alias (behavior := symbol)
syntax (name := aliasDefinition) &"type" ident "=" aiur_type ";" : aiur_alias
syntax (name := genericAlias) &"type" ident "<" sepBy1(ident, ",", ",", allowTrailingSep) ">"
  "=" aiur_type ";" : aiur_alias
syntax (name := aliasDecl) aiur_alias : aiur_decl
syntax:10 (name := orPattern) aiur_pattern:10 "|" aiur_pattern:11 : aiur_pattern
syntax:75 (name := loadPattern) "&" aiur_pattern:75 : aiur_pattern
syntax (name := globalPattern) "::" ident : aiur_pattern
syntax (name := globalExpr) "::" ident : aiur_expr
syntax (name := genericConstructorPattern) ident "::<" sepBy1(aiur_type, ",", ",", allowTrailingSep) ">"
  "::" ident : aiur_pattern
syntax (name := genericConstructorPatternArgs) ident "::<" sepBy1(aiur_type, ",", ",", allowTrailingSep) ">"
  "::" ident "(" sepBy(aiur_pattern, ",", ",", allowTrailingSep) ")" : aiur_pattern
declare_syntax_cat aiur_const (behavior := symbol)
syntax (name := constDefinition) &"const" ident "=" aiur_expr ";" : aiur_const
syntax (name := constDecl) aiur_const : aiur_decl
syntax (name := arrayType) "[" aiur_type ";" num "]" : aiur_type
syntax (name := arrayExpr) "[" sepBy(aiur_expr, ",", ",", allowTrailingSep) "]" : aiur_expr
syntax (name := repeatExpr) "[" aiur_expr ";" num "]" : aiur_expr
syntax (name := arrayPattern) "[" sepBy(aiur_pattern, ",", ",", allowTrailingSep) "]" : aiur_pattern
syntax (name := repeatPattern) "[" aiur_pattern ";" num "]" : aiur_pattern
syntax:80 (name := indexExpr) aiur_expr:80 "[" num "]" : aiur_expr
syntax:80 (name := sliceExpr) aiur_expr:80 "[" num ".." num "]" : aiur_expr
syntax:80 (name := sliceFromExpr) aiur_expr:80 "[" num ".." "]" : aiur_expr
syntax:80 (name := sliceToExpr) aiur_expr:80 "[" ".." num "]" : aiur_expr
syntax:80 (name := sliceAllExpr) aiur_expr:80 "[" ".." "]" : aiur_expr
syntax:80 (name := sliceInclusiveExpr) aiur_expr:80 "[" num "..=" num "]" : aiur_expr
syntax:80 (name := sliceToInclusiveExpr) aiur_expr:80 "[" "..=" num "]" : aiur_expr
syntax (name := namedBlock) "@" ident ":" "{" (aiur_body)? "}" : aiur_expr
syntax:10 (name := breakExpr) "break" "@" ident aiur_expr:11 : aiur_expr
syntax:10 (name := breakUnit) "break" "@" ident : aiur_expr
syntax:10 (name := returnExpr) "return" aiur_expr:11 : aiur_expr
syntax:10 (name := returnUnit) "return" : aiur_expr

declare_syntax_cat aiur_struct_field (behavior := symbol)
declare_syntax_cat aiur_struct (behavior := symbol)
declare_syntax_cat aiur_record_value (behavior := symbol)
declare_syntax_cat aiur_record_pattern_field (behavior := symbol)
declare_syntax_cat aiur_record_patterns (behavior := symbol)
syntax (name := structField) ident ":" aiur_type : aiur_struct_field
syntax (name := structDefinition) &"struct" ident "{" sepBy(aiur_struct_field, ",", ",", allowTrailingSep) "}" : aiur_struct
syntax (name := genericStruct) &"struct" ident "<" sepBy1(ident, ",", ",", allowTrailingSep) ">"
  "{" sepBy(aiur_struct_field, ",", ",", allowTrailingSep) "}" : aiur_struct
syntax (name := structDecl) aiur_struct : aiur_decl
syntax (name := recordValueField) ident ":" aiur_expr : aiur_record_value
syntax (name := recordValueShorthand) ident : aiur_record_value
syntax (name := recordExpr) atomic(ident "{" sepBy(aiur_record_value, ",", ",", allowTrailingSep) "}") : aiur_expr
syntax (name := genericRecordExpr) atomic(ident "::<" sepBy1(aiur_type, ",", ",", allowTrailingSep) ">"
  "{" sepBy(aiur_record_value, ",", ",", allowTrailingSep) "}") : aiur_expr
syntax:80 (name := memberExpr) aiur_expr:80 "." ident : aiur_expr
syntax (name := recordPatternField) ident ":" aiur_pattern : aiur_record_pattern_field
syntax (name := recordPatternShorthand) ident : aiur_record_pattern_field
syntax (name := recordPatternFields) sepBy(aiur_record_pattern_field, ",", ",", allowTrailingSep) (".." (",")?)? : aiur_record_patterns
syntax (name := recordPattern) ident "{" aiur_record_patterns "}" : aiur_pattern
syntax (name := genericRecordPattern) ident "::<" sepBy1(aiur_type, ",", ",", allowTrailingSep) ">"
  "{" aiur_record_patterns "}" : aiur_pattern

declare_syntax_cat aiur_update_step (behavior := symbol)
declare_syntax_cat aiur_update_entry (behavior := symbol)
syntax (name := updateMember) "." ident : aiur_update_step
syntax (name := updateProject) "." num : aiur_update_step
syntax (name := updateIndex) "[" num "]" : aiur_update_step
syntax (name := updateEntry) aiur_update_step+ "=" aiur_expr : aiur_update_entry
syntax:15 (name := updateExpr) aiur_expr:15 &"with" "{"
  sepBy(aiur_update_entry, ",", ",", allowTrailingSep) "}" : aiur_expr

def readName (s : Syntax) : Except String String :=
  match s.getId with
  | .str .anonymous n => .ok n
  | _ => .error "expected a simple identifier"

private def readLength (s : Syntax) : Except String Nat := do
  let some n := s.isNatLit? | throw "array lengths must be natural-number literals"
  checkArrayLength n
  return n

/-- Later frontends can extend shared syntax categories. Flat quotations keep
preferring their native alternatives when those extensions introduce ambiguity. -/
def nativeChoice (s : Syntax) : Syntax :=
  if s.getKind != `choice then s else
    (s.getArgs.find? fun child =>
      (`Aiur.Generic.Frontend).isPrefixOf child.getKind ||
        (`Aiur.Frontend).isPrefixOf child.getKind).getD s[0]

partial def type (params : List String) (s : Syntax) : Except String Ty := do
  if s.getKind == `choice then type params (nativeChoice s)
  else if s.getKind == ``pointerType then return .ptr (← type params s[1])
  else if s.getKind == ``arrayType then return .array (← type params s[1]) (← readLength s[3])
  else if s.getKind == ``namedType then
    let n ← readName s[0]
    return if n == "Field" then .field else if params.contains n then .param n else .named n []
  else if s.getKind == ``appliedType then
    let n ← readName s[0]
    if params.contains n then throw s!"type parameter '{n}' does not take arguments"
    return .named n (← s[2].getSepArgs.toList.mapM (type params))
  else if s.getKind == ``unitType then return .tuple []
  else if s.getKind == ``typeParens then type params s[1]
  else if s.getKind == ``tupleType then
    return .tuple ((← type params s[1]) :: (← s[3].getSepArgs.toList.mapM (type params)))
  else throw "expected an Aiur type"

partial def pattern (params : List String) (s : Syntax) : Except String (Pattern Nat) := do
  if s.getKind == `choice then pattern params (nativeChoice s)
  else if s.getKind == ``recordPattern || s.getKind == ``genericRecordPattern then
    let generic := s.getKind == ``genericRecordPattern
    let args ← if generic then s[2].getSepArgs.toList.mapM (type params) else pure []
    let fields := s[if generic then 5 else 2]
    let rest := !fields[1].getArgs.isEmpty
    let entries := fields[0].getSepArgs.toList
    if rest && !entries.isEmpty && fields[0].getArgs.size % 2 != 0 then
      throw "expected a comma before '..' in a struct pattern"
    let named ← entries.mapM fun entry => do
      let name ← readName entry[0]
      let pat ← if entry.getKind == ``recordPatternShorthand then pure (.bind name) else pattern params entry[2]
      return (name, pat)
    return .record { type := .named (← readName s[0]) args, fields := named.map Prod.fst, rest } (named.map Prod.snd)
  else if s.getKind == ``orPattern then
    let left ← pattern params s[0]
    return .orElse left (← pattern params s[2]) ⟨left.bindingNames, []⟩
  else if s.getKind == ``loadPattern then return .load (← pattern params s[1])
  else if s.getKind == ``globalPattern then return .global (← readName s[1])
  else if s.getKind == ``arrayPattern then return .array (← s[1].getSepArgs.toList.mapM (pattern params))
  else if s.getKind == ``repeatPattern then return .repeat (← pattern params s[1]) (← readLength s[3])
  else if s.getKind == ``literalPattern then return .literal (s[0].isNatLit?.getD 0)
  else if s.getKind == ``wildcardPattern then return .wildcard
  else if s.getKind == ``bindPattern then return .bind (← readName s[0])
  else if s.getKind == ``constructorPattern then return .construct (.named (← readName s[0]) []) (← readName s[2]) []
  else if s.getKind == ``constructorPatternArgs then
    return .construct (.named (← readName s[0]) []) (← readName s[2]) (← s[4].getSepArgs.toList.mapM (pattern params))
  else if s.getKind == ``genericConstructorPattern || s.getKind == ``genericConstructorPatternArgs then
    let ts ← s[2].getSepArgs.toList.mapM (type params)
    let ps ← if s.getKind == ``genericConstructorPatternArgs then
      s[7].getSepArgs.toList.mapM (pattern params) else pure []
    return .construct (.named (← readName s[0]) ts) (← readName s[5]) ps
  else if s.getKind == ``unitPattern then return .tuple []
  else if s.getKind == ``patternParens then pattern params s[1]
  else if s.getKind == ``tuplePattern then return .tuple ((← pattern params s[1]) :: (← s[3].getSepArgs.toList.mapM (pattern params)))
  else throw "expected an Aiur pattern"

/-- A terminal statement that can only exit has no implicit unit result.
Blocks are deliberately opaque here: their own breaks can complete normally. -/
private def exitsOnly : Expr α → Bool
  | .control (.exit _) _ => true
  | .letValue _ value body => exitsOnly value || exitsOnly body
  | .matchValue value arms => exitsOnly value || (!arms.isEmpty && (arms.map fun arm => exitsOnly arm.2).all id)
  | _ => false
termination_by expr => sizeOf expr
decreasing_by
  all_goals simp_wf
  all_goals first | omega | have h := List.sizeOf_lt_of_mem ‹_ ∈ _›; cases ‹_ × _›; simp_all only [Prod.mk.sizeOf_spec]; omega

partial def expr (params : List String) (s : Syntax) : Except String (Expr Nat) := do
  let k := s.getKind
  if k == `choice then
    -- A let followed by a trailing statement has both an expression parse
    -- and a statement parse. Preserve the lexical let scope in the latter.
    -- Prefer the binding before a sequence whose first expression might itself
    -- be a shorter let. Otherwise `let x = ...; check(x); x` loses x's scope.
    let selected := (s.getArgs.find? fun child =>
      child.getKind == ``bodyLet || child.getKind == ``bodyLetTyped).orElse fun _ =>
        s.getArgs.find? (·.getKind == ``bodySequence)
    expr params (selected.getD (nativeChoice s))
  else if k == ``bodyTail then expr params s[0]
  else if k == ``bodyEnd then
    let value ← expr params s[0]
    return if exitsOnly value then value else .letValue .wildcard value (.tuple [])
  else if k == ``bodySequence then return .letValue .wildcard (← expr params s[0]) (← expr params s[2])
  else if k == ``bodyLetEnd then return .letValue (← pattern params s[1]) (← expr params s[3]) (.tuple [])
  else if k == ``bodyLet then return .letValue (← pattern params s[1]) (← expr params s[3]) (← expr params s[5])
  else if k == ``bodyLetTyped || k == ``bodyLetTypedEnd then
    let body ← if k == ``bodyLetTyped then expr params s[7] else pure (.tuple [])
    return .letValue (← pattern params s[1])
      (.builtin (.ascribe (← type params s[3])) [← expr params s[5]]) body
  else if k == ``ascribeExpr then
    return .builtin (.ascribe (← type params s[3])) [← expr params s[1]]
  else if k == ``assertExpr || k == ``constrainExpr then
    let message := if s[5].getArgs.isEmpty then none else s[5][1].isStrLit?
    return .builtin (.assertEq ⟨message, k == ``assertExpr⟩) [← expr params s[2], ← expr params s[4]]
  else if k == ``debugExpr then
    let values ← if s[3].getArgs.isEmpty then pure [] else s[3][1].getSepArgs.toList.mapM (expr params)
    return .builtin (.debug (s[2].isStrLit?.getD "")) values
  else if k == ``blockStatements then
    if s[1].getArgs.isEmpty then return .tuple [] else expr params s[1][0]
  else if k == ``namedBlock then
    return .control (.block (← readName s[1]))
      (← if s[4].getArgs.isEmpty then pure (.tuple []) else expr params s[4][0])
  else if k == ``breakExpr then return .control (.exit (.block (← readName s[2]))) (← expr params s[3])
  else if k == ``breakUnit then return .control (.exit (.block (← readName s[2]))) (.tuple [])
  else if k == ``returnExpr then return .control (.exit .function) (← expr params s[1])
  else if k == ``returnUnit then return .control (.exit .function) (.tuple [])
  else if k == ``literal then return .literal (s[0].isNatLit?.getD 0)
  else if k == ``variableExpr then return .var (← readName s[0])
  else if k == ``globalExpr then return .global (← readName s[1])
  else if k == ``arrayExpr then return .array (← s[1].getSepArgs.toList.mapM (expr params))
  else if k == ``repeatExpr then return .repeat (← expr params s[1]) (← readLength s[3])
  else if k == ``indexExpr then return .index (← expr params s[0]) (s[2].isNatLit?.getD 0)
  else if k == ``sliceExpr || k == ``sliceInclusiveExpr then
    let stop := s[4].isNatLit?.getD 0
    return .slice (← expr params s[0]) (s[2].isNatLit?.getD 0)
      (some (if k == ``sliceInclusiveExpr then stop + 1 else stop))
  else if k == ``sliceFromExpr then return .slice (← expr params s[0]) (s[2].isNatLit?.getD 0) none
  else if k == ``sliceToExpr || k == ``sliceToInclusiveExpr then
    let stop := s[3].isNatLit?.getD 0
    return .slice (← expr params s[0]) 0 (some (if k == ``sliceToInclusiveExpr then stop + 1 else stop))
  else if k == ``sliceAllExpr then return .slice (← expr params s[0]) 0 none
  else if k == ``unitExpr then return .tuple []
  else if k == ``tupleExpr then return .tuple ((← expr params s[1]) :: (← s[3].getSepArgs.toList.mapM (expr params)))
  else if k == ``constructorExpr || k == ``constructorCall then
    let xs ← if k == ``constructorCall then s[4].getSepArgs.toList.mapM (expr params) else pure []
    return .construct (← readName s[0]) none (← readName s[2]) xs
  else if k == ``genericConstructor || k == ``genericConstructorArgs then
    let xs ← if k == ``genericConstructorArgs then s[7].getSepArgs.toList.mapM (expr params) else pure []
    return .construct (← readName s[0]) (some (← s[2].getSepArgs.toList.mapM (type params))) (← readName s[5]) xs
  else if k == ``call then return .call (← readName s[0]) none (← s[2].getSepArgs.toList.mapM (expr params))
  else if k == ``channelHintExpr then
    if (← readName s[0]) != "hint" then throw "only hint supports a channel"
    return .hint (← type params s[2]) (← expr params s[7]) (s[5].isStrLit?.getD "")
  else if k == ``genericCall || k == ``hintExpr then
    let n ← readName s[0]
    let ts ← if k == ``hintExpr then List.singleton <$> type params s[2] else s[2].getSepArgs.toList.mapM (type params)
    let xs ← if k == ``hintExpr then List.singleton <$> expr params s[5] else s[5].getSepArgs.toList.mapM (expr params)
    if n == "hint" then
      let [t] := ts | throw "hint takes one result type"
      let [x] := xs | throw "hint takes one key"
      return .hint t x
    return .call n (some ts) xs
  else if k == ``recordExpr || k == ``genericRecordExpr then
    let generic := k == ``genericRecordExpr
    let args ← if generic then s[2].getSepArgs.toList.mapM (type params) else pure []
    let named ← s[if generic then 5 else 2].getSepArgs.toList.mapM fun entry => do
      let name ← readName entry[0]
      let value ← if entry.getKind == ``recordValueShorthand then pure (.var name) else expr params entry[2]
      return (name, value)
    return .record { type := .named (← readName s[0]) args, fields := named.map Prod.fst } (named.map Prod.snd)
  else if k == ``updateExpr then
    let entries ← s[3].getSepArgs.toList.mapM fun entry => do
      let path ← entry[0].getArgs.toList.mapM fun step => do
        if step.getKind == ``updateMember then return UpdateStep.member { name := ← readName step[1] }
        else if step.getKind == ``updateProject then return UpdateStep.project (step[1].isNatLit?.getD 0)
        else if step.getKind == ``updateIndex then return UpdateStep.index (step[1].isNatLit?.getD 0)
        else throw "expected a field or static index in an update path"
      return (path, ← expr params entry[2])
    return .update (entries.map Prod.fst) ((← expr params s[0]) :: entries.map Prod.snd)
  else if k == ``memberExpr then return .member (← expr params s[0]) { name := ← readName s[2] }
  else if k == ``project then return .project (← expr params s[0]) (s[2].isNatLit?.getD 0)
  else if k == ``letValue then return .letValue (← pattern params s[1]) (← expr params s[3]) (← expr params s[5])
  else if k == ``parens || k == ``block then expr params s[1]
  else if k == ``store then return .store (← expr params s[1])
  else if k == ``load then return .load (← expr params s[1])
  else if k == ``neg then return .neg (← expr params s[1])
  else if k == ``add || k == ``sub || k == ``mul || k == ``div then
    let op := if k == ``add then BinOp.add else if k == ``sub then .sub else if k == ``mul then .mul else .div
    return .binary op (← expr params s[0]) (← expr params s[2])
  else if k == ``matchValue then
    return .matchValue (← expr params s[1]) (← s[3].getSepArgs.toList.mapM fun arm => return (← pattern params arm[0], ← expr params arm[2]))
  else throw s!"unsupported expression: {k}"

def lowerEnum (s : Syntax) : Except String EnumDecl := do
  let generic := s.getKind == ``genericEnum
  let ps ← if generic then s[3].getSepArgs.toList.mapM readName else pure []
  let cs := if generic then s[6] else s[3]
  return {
    name := ← readName s[1], typeParams := ps
    constructors := ← cs.getSepArgs.toList.mapM fun c => do
      let fields ← if c.getKind == ``payloadConstructor then c[2].getSepArgs.toList.mapM (type ps) else pure []
      return { name := ← readName c[0], fields }
  }

def lowerStruct (s : Syntax) : Except String StructDecl := do
  let generic := s.getKind == ``genericStruct
  let params ← if generic then s[3].getSepArgs.toList.mapM readName else pure []
  let fields ← s[if generic then 6 else 3].getSepArgs.toList.mapM fun field => do
    return (← readName field[0], ← type params field[2])
  return { name := ← readName s[1], typeParams := params, fields }

def lowerAlias (s : Syntax) : Except String AliasDecl := do
  let generic := s.getKind == ``genericAlias
  let ps ← if generic then s[3].getSepArgs.toList.mapM readName else pure []
  return {
    name := ← readName s[1], typeParams := ps
    target := ← type ps s[if generic then 6 else 3]
  }

partial def lowerFunction (enums : List EnumDecl) (aliases : List AliasDecl)
    (consts : List (ConstDecl Nat)) (s : Syntax) (checkParameters : Bool := true) : Except String (Function Nat) := do
  let s := if s.getKind == `choice then s[0] else s
  if s.getKind == ``inlineFunction then
    let definition ← lowerFunction enums aliases consts s[1] checkParameters
    if definition.isInline then throw "repeated inline modifier"
    return {definition with isInline := true}
  let generic := s.getKind == ``genericFunction
  let ps ← if generic then s[3].getSepArgs.toList.mapM readName else pure []
  let offset := if generic then 3 else 0
  let mut destructuring := []
  let mut inputs := []
  let mut boundNames := []
  for (param, i) in s[3 + offset].getSepArgs.toList.zipIdx do
    let pat ← pattern ps param[0]
    boundNames := boundNames ++ pat.bindingNames
    if checkParameters then
      let inspected ← Consts.expandPattern consts pat
      if !(← Aliases.expandPattern aliases inspected).irrefutable enums then throw "parameter patterns must be irrefutable"
    let t ← type ps param[2]
    match pat with
    | .bind n => inputs := inputs ++ [(n, t)]
    | _ =>
        let name := s!"$arg{i}"
        inputs := inputs ++ [(name, t)]
        destructuring := destructuring ++ [(pat, name)]
  if let some n := findDuplicate boundNames [] then throw s!"duplicate parameter binding '{n}'"
  let body ← if generic || s.getKind == ``functionStatements then
      if s[8 + offset].getArgs.isEmpty then pure (.tuple []) else expr ps s[8 + offset][0]
    else expr ps s[8 + offset]
  return {
    name := ← readName s[1], typeParams := ps, params := inputs
    result := ← type ps s[6 + offset]
    body := destructuring.foldr (fun (pat, n) b => .letValue pat (.var n) b) body
  }


/-- Strings are diagnostic metadata: comment masking, label rewriting and
operator spacing must never change their contents. -/
private inductive LexMode where
  | code
  | line
  | comment (depth : Nat)
  | string (escaped : Bool)

-- Accumulate in reverse so source length does not consume the interpreter stack.
private def prepareChars : List Char → LexMode → List Char → Except String (List Char)
  | [], .comment _, _ => .error "unterminated block comment"
  | [], .string _, _ => .error "unterminated diagnostic string"
  | [], _, acc => .ok acc.reverse
  | c :: rest, .string escaped, acc =>
      let mode := if escaped then LexMode.string false
        else if c == '\\' then .string true
        else if c == '"' then .code else .string false
      prepareChars rest mode (c :: acc)
  | c :: rest, .line, acc =>
      if c == '\n' then prepareChars rest .code (c :: acc)
      else prepareChars rest .line (' ' :: acc)
  | '/' :: '*' :: rest, .comment depth, acc =>
      prepareChars rest (.comment (depth + 1)) (' ' :: ' ' :: acc)
  | '*' :: '/' :: rest, .comment depth, acc =>
      prepareChars rest (if depth == 1 then .code else .comment (depth - 1)) (' ' :: ' ' :: acc)
  | c :: rest, .comment depth, acc =>
      prepareChars rest (.comment depth) ((if c == '\n' then c else ' ') :: acc)
  | '/' :: '/' :: rest, .code, acc => prepareChars rest .line (' ' :: ' ' :: acc)
  | '/' :: '*' :: rest, .code, acc => prepareChars rest (.comment 1) (' ' :: ' ' :: acc)
  | '"' :: rest, .code, acc => prepareChars rest (.string false) ('"' :: acc)
  | '.' :: '.' :: '=' :: rest, .code, acc =>
      prepareChars rest .code (' ' :: '=' :: '.' :: '.' :: ' ' :: acc)
  | '.' :: '.' :: rest, .code, acc => prepareChars rest .code (' ' :: '.' :: '.' :: ' ' :: acc)
  | c :: rest, .code, acc =>
      if c == '@' then .error "unexpected '@' in Aiur source" else
      if c == '\'' then prepareChars rest .code (' ' :: '@' :: acc) else
      if c == '.' then prepareChars rest .code (' ' :: '.' :: ' ' :: acc) else
      let c := if c == '\t' || c == '\r' then ' ' else c
      if c == '>' || c == '&' || c == '*' || ((c == '-' || c == '/') && rest.head? == some '-') then
        prepareChars rest .code (' ' :: c :: acc)
      else prepareChars rest .code (c :: acc)

/-- Shared lexical preparation for the modular frontend. -/
def prepareSource (source : String) : Except String String :=
  String.ofList <$> prepareChars source.toList .code []

/-- Elaborates Rust-like syntax without choosing either a field or entrypoints. -/
def ofString (env : Lean.Environment) (source : String) : Except String (Program Nat) := do
  let source ← prepareSource source
  let s ← Parser.runParserCategory env `aiur_program source "<aiur>"
  let ds := s[0].getArgs.toList
  let enums ← (ds.filter (·.getKind == ``enumDecl)).mapM (fun d => lowerEnum d[0])
  let structs ← (ds.filter (·.getKind == ``structDecl)).mapM (fun d => lowerStruct d[0])
  let aliases ← (ds.filter (·.getKind == ``aliasDecl)).mapM (fun d => lowerAlias d[0])
  let consts ← (ds.filter (·.getKind == ``constDecl)).mapM fun d => do
    return { name := ← readName d[0][1], value := ← Consts.ofExpr (← expr [] d[0][3]) : ConstDecl Nat }
  let expanded ← Aliases.resolveDeclarations ({ functions := [], enums, structs, aliases } : Program Nat)
  let resolved ← Consts.resolveDeclarations ({ functions := [], enums, structs, aliases, consts } : Program Nat)
  let functions ← (ds.filter (·.getKind == ``functionDecl)).mapM (fun d => lowerFunction (enums ++ structs.map StructDecl.signature) expanded resolved d[0])
  let tables ← (ds.filter (·.getKind == ``tableDecl)).mapM fun d => do
    let s := d[0]
    return { name := ← readName s[1], rowType := ← type [] s[3], rows := ← s[5].getSepArgs.toList.mapM (expr []) : Table Nat }
  let maps ← (ds.filter (·.getKind == ``mapDecl)).mapM fun d => do
    let s := nativeChoice d[0]
    let params ← s[3].getSepArgs.toList.mapM fun param => do
      let .bind n ← pattern [] param[0] | throw "map parameters must be named bindings"
      return (n, ← type [] param[2])
    return { name := ← readName s[1], params, result := ← type [] s[6], input := ← readName s[8], output := ← readName s[10] : MapDecl }
  return (← prepare { functions, enums, structs, tables, maps, aliases, consts }).program

/-- The ordinary quotation supports the source AST when that type is expected.
Existing quotations of the monomorphic core remain compatible. -/
@[term_elab Aiur.Frontend.aiurTerm]
def elabGeneric : TermElab := fun stx expected => do
  let some expected := expected | throwUnsupportedSyntax
  unless (← Meta.whnf expected).isAppOf ``Program do throwUnsupportedSyntax
  match ofString (← getEnv) (stx[1].isStrLit?.getD "") with
  | .error e => throwErrorAt stx[1] "{e}"
  | .ok p => return Lean.toExpr p

/-- An explicit spelling is useful when the expected type is not yet known. -/
elab "aiur_generic% " source:str : term => do
  match ofString (← getEnv) source.getString with
  | .error e => throwErrorAt source "{e}"
  | .ok p => return Lean.toExpr p

end Aiur.Generic.Frontend
