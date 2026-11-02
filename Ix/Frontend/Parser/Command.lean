/-
  Ix.Frontend.Parser.Command: Pure, total top-level command and module parser
  for the Ix Frontend (`import #<hash>`, `import Mod`, `map Name := #<hash>`,
  `def`, `abbrev`, `theorem`, `axiom`, `opaque`, `instance`, `inductive`,
  `structure`, `class`, `namespace`, `section`, `end`, `variable`, `universe`,
  `open`, `mutual`, and operator declarations).
-/
module

public import Ix.Frontend.Parser.Term

@[expose] public section

namespace Ix.Frontend.Parser

/-! ## Declaration Modifiers & Header Helpers -/

/-- Parse zero or more declaration modifiers (`private`, `protected`, `noncomputable`, `partial`, `unsafe`). -/
def declModifiersLoop (ctx : IxParserContext) (s : ParserState) : Nat → ParserState
  | 0 => s
  | fuel + 1 =>
    let (tok?, s) := peekToken ctx s
    match tok? with
    | some (.atom _ kw) =>
      if kw == "private" || kw == "protected" || kw == "noncomputable" ||
         kw == "partial" || kw == "unsafe" then
        let s := tokenFn ctx s
        declModifiersLoop ctx s fuel
      else
        s
    | _ => s

def declModifiersFn : ParserFn := fun ctx s =>
  let iniSz := s.stackSize
  let s := declModifiersLoop ctx s 8
  s.mkNode SyntaxKind.modifiersKind iniSz

/-- Parse a declaration identifier with optional `.{u, v}` universe parameters:
    pushes `ident` and a `SyntaxKind.univParamsKind` node. -/
def declIdFn : ParserFn := fun ctx s =>
  (identFn ctx s).bindState fun s =>
    if s.hasError then s else
    let (tok?, s) := peekToken ctx s
    match tok? with
    | some (.atom _ ".{") =>
      let iniSz := s.stackSize
      let s := symbolFn ".{" ctx s
      let s := sepBy1Fn identFn (symbolFn ",") false ctx s
      (symbolFn "}" ctx s).bindState fun s =>
        if s.hasError then s else
        let paramsNull := s.stxStack.getD (iniSz + 1)
        let s := s.shrinkStack iniSz
        s.pushSyntax (Syntax.mkNode SyntaxKind.univParamsKind (Syntax.getArgs paramsNull))
    | _ =>
      s.pushSyntax (Syntax.mkNode SyntaxKind.univParamsKind #[])

/-- Parse zero or more bracketed or simple binders on a declaration signature. -/
def declBindersFn : ParserFn :=
  manyFn (bracketedBinderFn termFn)

/-- Parse optional `: valuePrefix? type` return type annotation on a declaration.
    Pushes `valuePrefix` and `typeOrNull`. -/
def optDeclSigTypeFn : ParserFn := fun ctx s =>
  let (tok?, s) := peekToken ctx s
  match tok? with
  | some (.atom _ ":") =>
    (symbolFn ":" ctx s).bindState fun s =>
      let s := s.popSyntax -- drop `:`
      (valuePrefixFn ctx s).bindState fun s =>
        termFn { ctx with prec := 0 } s
  | _ =>
    let s := s.pushSyntax (Syntax.mkNode SyntaxKind.valuePrefix #[])
    s.pushSyntax (Syntax.mkNullNode #[])

/-- Parse `: valuePrefix? type` (required) on `axiom` / `theorem` / `instance`.
    Pushes `valuePrefix` and `type`. -/
def reqDeclSigTypeFn : ParserFn := fun ctx s =>
  let s := symbolFn ":" ctx s
  if s.hasError then s else
  let s := s.popSyntax -- drop `:`
  let s := valuePrefixFn ctx s
  termFn { ctx with prec := 0 } s

/-! ## Inductive Constructors & Structure Fields -/

/-- Check if the next token starts a new top-level command (used to terminate
    un-delimited `structure` field lists or `inductive` constructor lists). -/
def isCommandStart (tok : Ix.Syntax) : Bool :=
  match tok with
  | .atom _ kw =>
    kw == "def" || kw == "abbrev" || kw == "theorem" || kw == "lemma" ||
    kw == "axiom" || kw == "opaque" || kw == "instance" ||
    kw == "inductive" || kw == "structure" || kw == "class" ||
    kw == "mutual" || kw == "end" || kw == "namespace" || kw == "section" ||
    kw == "open" || kw == "export" || kw == "variable" || kw == "universe" ||
    kw == "import" || kw == "private" || kw == "protected" ||
    kw == "noncomputable" || kw == "partial" || kw == "unsafe" ||
    kw == "deriving"
  | .ident _ _ (.str (.anonymous _) w _) _ =>
    w == "map" || w == "infixl" || w == "infixr" || w == "notation"
  | _ => false

/-- Parse a single inductive constructor `| ctorName binders* [: type]`. -/
def ctorDeclFn : ParserFn := fun ctx s =>
  let iniSz := s.stackSize
  let s := symbolFn "|" ctx s
  if s.hasError then s else
  let s := identFn ctx s
  if s.hasError then s else
  let s := declBindersFn ctx s
  if s.hasError then s else
  let s := optDeclSigTypeFn ctx s
  if s.hasError then s else
  s.mkNode SyntaxKind.ctorDecl iniSz

/-- Parse an optional `deriving C1, C2` clause at the end of an `inductive` or `structure`. -/
def optDerivingFn : ParserFn := fun ctx s =>
  let (tok?, s) := peekToken ctx s
  match tok? with
  | some (.atom _ "deriving") =>
    let s := symbolFn "deriving" ctx s
    let s := s.popSyntax
    sepBy1Fn identFn (symbolFn ",") false ctx s
  | _ =>
    s.pushSyntax (Syntax.mkNullNode #[])

/-- Parse a single structure/class field declaration:
    either `(0 field1 field2 : !Type)` or `field1 : !Type [:= default]`. -/
def structFieldDeclFn : ParserFn := fun ctx s =>
  let (tok?, s) := peekToken ctx s
  match tok? with
  | none => s.mkEOIError ["field declaration"]
  | some tok =>
    if isCommandStart tok || Syntax.getAtomVal tok == "|" then
      s.mkUnexpectedError "end of structure fields"
    else
      let iniSz := s.stackSize
      match tok with
      | .atom _ "(" | .atom _ "{" =>
        let closeSym := if Syntax.getAtomVal tok == "(" then ")" else "}"
        let s := tokenFn ctx s
        let s := binderPrefixFn ctx s
        let s := many1Fn identFn ctx s
        let s := symbolFn ":" ctx s
        let s := valuePrefixFn ctx s
        let s := termFn { ctx with prec := 0 } s
        let s := optionalFn (seqFn (symbolFn ":=") (withPrecFn 0 termFn)) ctx s
        let s := symbolFn closeSym ctx s
        s.mkNode SyntaxKind.fieldDecl iniSz
      | _ =>
        let s := binderPrefixFn ctx s
        let s := many1Fn identFn ctx s
        if s.hasError then s else
        let s := symbolFn ":" ctx s
        if s.hasError then s else
        let s := valuePrefixFn ctx s
        let s := termFn { ctx with prec := 0 } s
        let s := optionalFn (seqFn (symbolFn ":=") (withPrecFn 0 termFn)) ctx s
        s.mkNode SyntaxKind.fieldDecl iniSz

/-! ## Top-Level Command Parser -/

/-- Parse a `def`, `abbrev`, `theorem`/`lemma`, or `opaque` declaration after its modifiers. -/
def parseValueDecl (kind : Ix.Name) : ParserFn := fun ctx s =>
  s.bindState fun s =>
    let iniSz := s.stackSize - 1 -- include the already-pushed `modifiers` node
    (tokenFn ctx s).bindState fun s =>       -- consume keyword (`def`, `theorem`, etc.)
    (declIdFn ctx s).bindState fun s =>
      if s.hasError then s else
      (declBindersFn ctx s).bindState fun s =>
        if s.hasError then s else
        (optDeclSigTypeFn ctx s).bindState fun s =>
          if s.hasError then s else
          let (tok?, s) := peekToken ctx s
          match tok? with
          | some (.atom _ ":=") =>
            (symbolFn ":=" ctx s).bindState fun s =>
            (termFn { ctx with prec := 0 } s).bindState fun s =>
              s.mkNode kind iniSz
          | some (.atom _ "|") =>
            -- Pattern-matching definition `def f : Nat → Nat | 0 => 1 | n => n`
            (many1Fn (matchAltFn termFn) ctx s).bindState fun s =>
              s.mkNode kind iniSz
          | _ =>
            (symbolFn ":=" ctx s).bindState fun s =>
              s.mkNode kind iniSz

/-- Parse an `axiom` declaration after its modifiers. -/
def parseAxiomDecl : ParserFn := fun ctx s =>
  let iniSz := s.stackSize - 1
  let s := tokenFn ctx s -- consume `axiom`
  let s := declIdFn ctx s
  if s.hasError then s else
  let s := declBindersFn ctx s
  if s.hasError then s else
  let s := reqDeclSigTypeFn ctx s
  s.mkNode SyntaxKind.axiomDecl iniSz

/-- Parse an `instance` declaration after its modifiers:
    `instance [name?] binders* : Class args := body` (or `where field := val ...`). -/
def parseInstanceDecl : ParserFn := fun ctx s =>
  let iniSz := s.stackSize - 1
  let s := tokenFn ctx s -- consume `instance`
  -- Optional instance name (if next token is an `ident`, consume it via `declIdFn`; otherwise synthesize anonymous)
  let (tok?, s) := peekToken ctx s
  let s := match tok? with
    | some (.ident ..) => declIdFn ctx s
    | _ =>
      let s := s.pushSyntax (Syntax.mkSimpleIdent Name.mkAnon)
      s.pushSyntax (Syntax.mkNode SyntaxKind.univParamsKind #[])
  if s.hasError then s else
  let s := declBindersFn ctx s
  if s.hasError then s else
  let s := reqDeclSigTypeFn ctx s
  if s.hasError then s else
  let (bodyTok?, s) := peekToken ctx s
  match bodyTok? with
  | some (.atom _ "where") =>
    let s := symbolFn "where" ctx s
    let fieldAssign : ParserFn := fun c st =>
      let fSz := st.stackSize
      let st := optionalFn (symbolFn "|") c st
      let st := st.popSyntax
      let st := identFn c st
      if st.hasError then st else
      let st := manyFn (simpleOrBracketedBinderFn termFn) c st
      let st := symbolFn ":=" c st
      let st := termFn { c with prec := 0 } st
      st.mkNode SyntaxKind.structFieldAssign fSz
    let s := manyFn fieldAssign ctx s
    s.mkNode SyntaxKind.instanceDecl iniSz
  | _ =>
    let s := symbolFn ":=" ctx s
    let s := termFn { ctx with prec := 0 } s
    s.mkNode SyntaxKind.instanceDecl iniSz

/-- Parse an `inductive` declaration after its modifiers. -/
def parseInductiveDecl : ParserFn := fun ctx s =>
  let iniSz := s.stackSize - 1
  let s := tokenFn ctx s -- consume `inductive`
  let s := declIdFn ctx s
  if s.hasError then s else
  let s := declBindersFn ctx s
  if s.hasError then s else
  let s := optDeclSigTypeFn ctx s
  if s.hasError then s else
  let s := optionalFn (symbolFn "where") ctx s
  let s := s.popSyntax -- drop optional `where` wrapper
  let s := manyFn ctorDeclFn ctx s
  let s := optDerivingFn ctx s
  s.mkNode SyntaxKind.inductiveDecl iniSz

/-- Parse a `structure` or `class` declaration after its modifiers. -/
def parseStructureOrClassDecl (kind : Ix.Name) : ParserFn := fun ctx s =>
  let iniSz := s.stackSize - 1
  let s := tokenFn ctx s -- consume `structure` or `class`
  let s := declIdFn ctx s
  if s.hasError then s else
  let s := declBindersFn ctx s
  if s.hasError then s else
  -- Optional `extends P1, P2`
  let (extTok?, s) := peekToken ctx s
  let s := match extTok? with
    | some (.atom _ "extends") | some (.atom _ "extending") =>
      let s := tokenFn ctx s
      let s := s.popSyntax
      sepBy1Fn (withPrecFn 0 termFn) (symbolFn ",") false ctx s
    | _ =>
      s.pushSyntax (Syntax.mkNullNode #[])
  if s.hasError then s else
  let s := optDeclSigTypeFn ctx s
  if s.hasError then s else
  let (whereTok?, s) := peekToken ctx s
  let s := match whereTok? with
    | some (.atom _ "where") | some (.atom _ ":=") =>
      let s := tokenFn ctx s
      let s := s.popSyntax
      -- Optional custom constructor `mk ::`
      let customCtorAttempt : ParserFn := fun c st =>
        let st := identFn c st
        if st.hasError then st else
        let st := symbolFn "::" c st
        if st.hasError then st else
        st.popSyntax -- keep just `ident`
      let noCustomCtor : ParserFn := fun _ st =>
        st.pushSyntax (Syntax.mkNullNode #[])
      let s := tryOrElseFn customCtorAttempt noCustomCtor ctx s
      -- Check if this is an inductive-style `class` with `| ctor` branches or field list
      let (next?, s) := peekToken ctx s
      match next? with
      | some (.atom _ "|") =>
        manyFn ctorDeclFn ctx s
      | _ =>
        manyFn structFieldDeclFn ctx s
    | _ =>
      let s := s.pushSyntax (Syntax.mkNullNode #[])
      s.pushSyntax (Syntax.mkNullNode #[])
  let s := optDerivingFn ctx s
  s.mkNode kind iniSz

/-- Parse a single top-level command, structurally recursive on `fuel : Nat` (for `mutual ... end`). -/
def commandStep : Nat → ParserFn
  | 0 => fun _ s => s.mkUnexpectedError "parser fuel exhausted in command"
  | fuel + 1 => fun ctx s =>
    let (tok?, s) := peekToken ctx s
    match tok? with
    | none => s.mkEOIError ["command"]
    | some (.atom _ kw) =>
      match kw with
      | "import" =>
        let iniSz := s.stackSize
        let s := symbolFn "import" ctx s
        let (next?, s) := peekToken ctx s
        match next? with
        | some (.node _ k _) =>
          if k == SyntaxKind.hashRef then
            let s := hashRefFn ctx s
            s.mkNode SyntaxKind.hashImport iniSz
          else
            s.mkUnexpectedError "expected module name or #<hash> after 'import'"
        | _ =>
          let s := identFn ctx s
          if s.hasError then s else
          -- Optional `@ #<hash>` pin on named import
          let (atTok?, s) := peekToken ctx s
          let s := match atTok? with
            | some (.atom _ "@") =>
              let s := symbolFn "@" ctx s
              let s := s.popSyntax
              hashRefFn ctx s
            | _ =>
              s.pushSyntax (Syntax.mkNullNode #[])
          s.mkNode SyntaxKind.importDecl iniSz
      | "namespace" =>
        let iniSz := s.stackSize
        let s := symbolFn "namespace" ctx s
        let s := identFn ctx s
        s.mkNode SyntaxKind.namespaceDecl iniSz
      | "section" =>
        let iniSz := s.stackSize
        let s := symbolFn "section" ctx s
        let s := optionalFn identFn ctx s
        s.mkNode SyntaxKind.sectionDecl iniSz
      | "end" =>
        let iniSz := s.stackSize
        let s := symbolFn "end" ctx s
        let s := optionalFn identFn ctx s
        s.mkNode SyntaxKind.endDecl iniSz
      | "universe" =>
        let iniSz := s.stackSize
        let s := symbolFn "universe" ctx s
        let s := many1Fn identFn ctx s
        s.mkNode SyntaxKind.universeDecl iniSz
      | "variable" =>
        let iniSz := s.stackSize
        let s := symbolFn "variable" ctx s
        let s := many1Fn (bracketedBinderFn termFn) ctx s
        s.mkNode SyntaxKind.variableDecl iniSz
      | "open" =>
        let iniSz := s.stackSize
        let s := symbolFn "open" ctx s
        let s := many1Fn identFn ctx s
        let s := optionalFn (fun c st =>
          let st := symbolFn "(" c st
          let st := many1Fn identFn c st
          symbolFn ")" c st) ctx s
        s.mkNode SyntaxKind.openDecl iniSz
      | "mutual" =>
        let iniSz := s.stackSize
        let s := symbolFn "mutual" ctx s
        let notEnd : ParserFn := fun c st =>
          let (t?, st) := peekToken c st
          match t? with
          | some (.atom _ "end") | none => st.mkUnexpectedError "end of mutual block"
          | _ => commandStep fuel c st
        let s := many1Fn notEnd ctx s
        let s := symbolFn "end" ctx s
        s.mkNode SyntaxKind.mutualDecl iniSz
      | _ =>
        -- Declaration with optional modifiers (`private`, `protected`, `noncomputable`, etc.)
        let s := declModifiersFn ctx s
        let (declTok?, s) := peekToken ctx s
        match declTok? with
        | some (.atom _ dkw) =>
          match dkw with
          | "def"                  => parseValueDecl SyntaxKind.defDecl ctx s
          | "abbrev"               => parseValueDecl SyntaxKind.abbrevDecl ctx s
          | "theorem" | "lemma"    => parseValueDecl SyntaxKind.theoremDecl ctx s
          | "opaque"               => parseValueDecl SyntaxKind.opaqueDecl ctx s
          | "axiom"                => parseAxiomDecl ctx s
          | "instance"             => parseInstanceDecl ctx s
          | "inductive"            => parseInductiveDecl ctx s
          | "structure"            => parseStructureOrClassDecl SyntaxKind.structureDecl ctx s
          | "class"                => parseStructureOrClassDecl SyntaxKind.classDecl ctx s
          | _ => s.mkUnexpectedError s!"unexpected keyword '{dkw}' at top level"
        | _ => s.mkUnexpectedError "expected declaration keyword after modifiers"
    | some (.ident _ _ (.str (.anonymous _) word _) _) =>
      if word == "map" then
        -- First-class programmable `Name -> Address` mapping: `map Foo.Bar := #<64-hex>`
        let iniSz := s.stackSize
        let s := nonReservedSymbolFn "map" ctx s
        let s := identFn ctx s
        let s := symbolFn ":=" ctx s
        let s := hashRefFn ctx s
        s.mkNode SyntaxKind.buildMapDecl iniSz
      else if word == "infixl" || word == "infixr" || word == "infix" then
        let iniSz := s.stackSize
        let s := tokenFn ctx s
        let s := optionalFn (seqFn (symbolFn ":") numLitFn) ctx s
        let s := strLitFn ctx s
        let s := orelseFn (symbolFn "=>") (symbolFn "↦") ctx s
        let s := identFn ctx s
        s.mkNode SyntaxKind.notationDecl iniSz
      else
        s.mkUnexpectedError s!"unexpected identifier '{word}' at top level"
    | _ =>
      s.mkUnexpectedError "expected top-level command"

def commandFn : ParserFn := commandStep 64

/-! ## Module Parser & Dynamic Operator Registration -/

/-- If `cmd` is a `notationDecl` (`infixl:65 " ++ " => append`), update `env` with the new operator. -/
def updateParserEnvFromCommand (env : IxParserEnv) (cmd : Ix.Syntax) : IxParserEnv :=
  if Syntax.isOfKind cmd SyntaxKind.notationDecl then
    let args := Syntax.getArgs cmd
    let fixStr := Syntax.getNameOrAtom args[0]?
    let fixity : FixityKind :=
      if fixStr == "infixr" then .infixr
      else if fixStr == "infix" then .infixn
      else .infixl
    let prec : Nat := match args[1]? with
      | some optNode =>
        let numNode := Syntax.getArg optNode 1
        match Syntax.getArg numNode 0 with
        | .atom _ nStr => (parseNatLiteral nStr).getD 65
        | _ => 65
      | none => 65
    let rawSym := match args[2]? with
      | some strNode =>
        match Syntax.getArg strNode 0 with
        | .atom _ s => String.ofList (s.toList.filter (!isSpaceChar ·))
        | _ => ""
      | none => ""
    let target := match args[4]? with
      | some stx =>
        let id := Syntax.getId stx
        if Name.isAnonymous id then none else some id
      | none => none
    if rawSym.isEmpty then env
    else env.addOperator { symbol := rawSym, kind := SyntaxKind.binOpTerm, fixity, prec, targetFn := target }
  else
    env
where
  Syntax.getNameOrAtom : Option Ix.Syntax → String
    | some (.ident _ _ (.str (.anonymous _) s _) _) => s
    | some (.atom _ s) => s
    | _ => ""

/-- Loop parsing top-level commands until EOI, updating `IxParserEnv` when notation commands occur. -/
def parseModuleLoop (inputCtx : InputContext) (env : IxParserEnv) (s : ParserState)
    (cmds : Array Ix.Syntax) : Nat → Except String (Ix.Syntax × IxParserEnv)
  | 0 => .error "parser fuel exhausted in module loop"
  | fuel + 1 =>
    s.bindState fun s =>
      let ctx : IxParserContext := { inputCtx, env, prec := 0 }
      if atEOI ctx s then
        .ok (Syntax.mkNode SyntaxKind.moduleKind cmds, env)
      else
        let iniSz := s.stackSize
        (commandFn ctx s).bindState fun s' =>
          match s'.errorMsg with
          | some err => .error (ParserError.toString inputCtx err)
          | none =>
            let cmd := s'.stxStack.back
            let env' := updateParserEnvFromCommand env cmd
            let sClean := s'.shrinkStack iniSz
            parseModuleLoop inputCtx env' sClean (cmds.push cmd) fuel

/-- Parse a complete `.ix` / `.lean` source string into a `SyntaxKind.moduleKind` AST
    and the resulting `IxParserEnv`. 100% pure and deterministic (zero `IO`). -/
def parseModuleWithEnv (input : String) (fileName : String := "<input>")
    (env : IxParserEnv := defaultParserEnv) : Except String (Ix.Syntax × IxParserEnv) :=
  let inputCtx := InputContext.mkInputContext input fileName
  parseModuleLoop inputCtx env {} #[] (inputCtx.charCount + 16)

/-- Parse a complete `.ix` / `.lean` source string into an `Ix.Syntax` tree. -/
def parseModule (input : String) (fileName : String := "<input>")
    (env : IxParserEnv := defaultParserEnv) : Except String Ix.Syntax := do
  let (stx, _) ← parseModuleWithEnv input fileName env
  return stx

end Ix.Frontend.Parser
