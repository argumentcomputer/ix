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
    bindPeek ctx s fun tok? s =>
      match tok? with
      | some (.atom _ kw) =>
        if kw == "private" || kw == "protected" || kw == "noncomputable" ||
           kw == "partial" || kw == "unsafe" then
          (tokenFn ctx s).bindState fun s =>
            declModifiersLoop ctx s fuel
        else
          s
      | _ => s

def declModifiersFn : ParserFn := fun ctx s =>
  s.bindState fun s =>
    let iniSz := s.stackSize
    (declModifiersLoop ctx s 8).bindState fun s =>
      s.mkNode SyntaxKind.modifiersKind iniSz

/-- Parse a declaration identifier with optional `.{u, v}` universe parameters:
    pushes `ident` and a `SyntaxKind.univParamsKind` node. -/
def declIdFn : ParserFn := fun ctx s =>
  (identFn ctx s).bindState fun s =>
    if s.hasError then s else
    bindPeek ctx s fun tok? s =>
      match tok? with
      | some (.atom _ ".{") =>
        let iniSz := s.stackSize
        (symbolFn ".{" ctx s).bindState fun s =>
        (sepBy1Fn identFn (symbolFn ",") false ctx s).bindState fun s =>
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
  bindPeek ctx s fun tok? s =>
    match tok? with
    | some (.atom _ ":") =>
      (symbolFn ":" ctx s).bindState fun s =>
        let s := s.popSyntax -- drop `:`
        (valuePrefixFn ctx s).bindState fun s =>
          withPrecFn 0 termFn ctx s
    | _ =>
      let s := s.pushSyntax (Syntax.mkNode SyntaxKind.valuePrefix #[])
      s.pushSyntax (Syntax.mkNullNode #[])

/-- Parse `: valuePrefix? type` (required) on `axiom` / `theorem` / `instance`.
    Pushes `valuePrefix` and `type`. -/
def reqDeclSigTypeFn : ParserFn := fun ctx s =>
  (symbolFn ":" ctx s).bindState fun s =>
    if s.hasError then s else
    let s := s.popSyntax -- drop `:`
    (valuePrefixFn ctx s).bindState fun s =>
      withPrecFn 0 termFn ctx s

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
  s.bindState fun s =>
    let iniSz := s.stackSize
    (symbolFn "|" ctx s).bindState fun s =>
      if s.hasError then s else
      (identFn ctx s).bindState fun s =>
        if s.hasError then s else
        (declBindersFn ctx s).bindState fun s =>
          if s.hasError then s else
          (optDeclSigTypeFn ctx s).bindState fun s =>
            if s.hasError then s else
            s.mkNode SyntaxKind.ctorDecl iniSz

/-- Parse an optional `deriving C1, C2` clause at the end of an `inductive` or `structure`. -/
def optDerivingFn : ParserFn := fun ctx s =>
  bindPeek ctx s fun tok? s =>
    match tok? with
    | some (.atom _ "deriving") =>
      (symbolFn "deriving" ctx s).bindState fun s =>
        let s := s.popSyntax
        sepBy1Fn identFn (symbolFn ",") false ctx s
    | _ =>
      s.pushSyntax (Syntax.mkNullNode #[])

/-- Parse a single structure/class field declaration:
    either `(0 field1 field2 : !Type)` or `field1 : !Type [:= default]`. -/
def structFieldDeclFn : ParserFn := fun ctx s =>
  bindPeek ctx s fun tok? s =>
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
          (tokenFn ctx s).bindState fun s =>
          (binderPrefixFn ctx s).bindState fun s =>
          (many1Fn identFn ctx s).bindState fun s =>
          (symbolFn ":" ctx s).bindState fun s =>
          (valuePrefixFn ctx s).bindState fun s =>
          (withPrecFn 0 termFn ctx s).bindState fun s =>
          (optionalFn (seqFn (symbolFn ":=") (withPrecFn 0 termFn)) ctx s).bindState fun s =>
          (symbolFn closeSym ctx s).bindState fun s =>
            s.mkNode SyntaxKind.fieldDecl iniSz
        | _ =>
          (binderPrefixFn ctx s).bindState fun s =>
          (many1Fn identFn ctx s).bindState fun s =>
            if s.hasError then s else
            (symbolFn ":" ctx s).bindState fun s =>
              if s.hasError then s else
              (valuePrefixFn ctx s).bindState fun s =>
              (withPrecFn 0 termFn ctx s).bindState fun s =>
              (optionalFn (seqFn (symbolFn ":=") (withPrecFn 0 termFn)) ctx s).bindState fun s =>
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
          bindPeek ctx s fun tok? s =>
            match tok? with
            | some (.atom _ ":=") =>
              (symbolFn ":=" ctx s).bindState fun s =>
              (withPrecFn 0 termFn ctx s).bindState fun s =>
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
  s.bindState fun s =>
    let iniSz := s.stackSize - 1
    (tokenFn ctx s).bindState fun s => -- consume `axiom`
    (declIdFn ctx s).bindState fun s =>
      if s.hasError then s else
      (declBindersFn ctx s).bindState fun s =>
        if s.hasError then s else
        (reqDeclSigTypeFn ctx s).bindState fun s =>
          s.mkNode SyntaxKind.axiomDecl iniSz

/-- Parse an `instance` declaration after its modifiers:
    `instance [name?] binders* : Class args := body` (or `where field := val ...`). -/
def parseInstanceDecl : ParserFn := fun ctx s =>
  s.bindState fun s =>
    let iniSz := s.stackSize - 1
    (tokenFn ctx s).bindState fun s => -- consume `instance`
      -- Optional instance name (if next token is an `ident`, consume it via `declIdFn`; otherwise synthesize anonymous)
      bindPeek ctx s fun tok? s =>
        let sAfterId := match tok? with
          | some (.ident ..) => declIdFn ctx s
          | _ =>
            let s := s.pushSyntax (Syntax.mkSimpleIdent Name.mkAnon)
            s.pushSyntax (Syntax.mkNode SyntaxKind.univParamsKind #[])
        sAfterId.bindState fun s =>
          if s.hasError then s else
          (declBindersFn ctx s).bindState fun s =>
            if s.hasError then s else
            (reqDeclSigTypeFn ctx s).bindState fun s =>
              if s.hasError then s else
              bindPeek ctx s fun bodyTok? s =>
                match bodyTok? with
                | some (.atom _ "where") =>
                  (symbolFn "where" ctx s).bindState fun s =>
                    let fieldAssign : ParserFn := fun c st =>
                      let fSz := st.stackSize
                      (optionalFn (symbolFn "|") c st).bindState fun st =>
                        let st := st.popSyntax
                        (identFn c st).bindState fun st =>
                          if st.hasError then st else
                          (manyFn (simpleOrBracketedBinderFn termFn) c st).bindState fun st =>
                          (symbolFn ":=" c st).bindState fun st =>
                          (withPrecFn 0 termFn c st).bindState fun st =>
                            st.mkNode SyntaxKind.structFieldAssign fSz
                    (manyFn fieldAssign ctx s).bindState fun s =>
                      s.mkNode SyntaxKind.instanceDecl iniSz
                | _ =>
                  (symbolFn ":=" ctx s).bindState fun s =>
                  (withPrecFn 0 termFn ctx s).bindState fun s =>
                    s.mkNode SyntaxKind.instanceDecl iniSz

/-- Parse an `inductive` declaration after its modifiers. -/
def parseInductiveDecl : ParserFn := fun ctx s =>
  s.bindState fun s =>
    let iniSz := s.stackSize - 1
    (tokenFn ctx s).bindState fun s => -- consume `inductive`
    (declIdFn ctx s).bindState fun s =>
      if s.hasError then s else
      (declBindersFn ctx s).bindState fun s =>
        if s.hasError then s else
        (optDeclSigTypeFn ctx s).bindState fun s =>
          if s.hasError then s else
          (optionalFn (symbolFn "where") ctx s).bindState fun s =>
            let s := s.popSyntax -- drop optional `where` wrapper
            (manyFn ctorDeclFn ctx s).bindState fun s =>
            (optDerivingFn ctx s).bindState fun s =>
              s.mkNode SyntaxKind.inductiveDecl iniSz

/-- Parse a `structure` or `class` declaration after its modifiers. -/
def parseStructureOrClassDecl (kind : Ix.Name) : ParserFn := fun ctx s =>
  s.bindState fun s =>
    let iniSz := s.stackSize - 1
    (tokenFn ctx s).bindState fun s => -- consume `structure` or `class`
    (declIdFn ctx s).bindState fun s =>
      if s.hasError then s else
      (declBindersFn ctx s).bindState fun s =>
        if s.hasError then s else
        -- Optional `extends P1, P2`
        bindPeek ctx s fun extTok? s =>
          let sAfterExt := match extTok? with
            | some (.atom _ "extends") | some (.atom _ "extending") =>
              (tokenFn ctx s).bindState fun s =>
                let s := s.popSyntax
                sepBy1Fn (withPrecFn 0 termFn) (symbolFn ",") false ctx s
            | _ =>
              s.pushSyntax (Syntax.mkNullNode #[])
          sAfterExt.bindState fun s =>
            if s.hasError then s else
            (optDeclSigTypeFn ctx s).bindState fun s =>
              if s.hasError then s else
              bindPeek ctx s fun whereTok? s =>
                let sAfterBody := match whereTok? with
                  | some (.atom _ "where") | some (.atom _ ":=") =>
                    (tokenFn ctx s).bindState fun s =>
                      let s := s.popSyntax
                      -- Optional custom constructor `mk ::`
                      let customCtorAttempt : ParserFn := fun c st =>
                        (identFn c st).bindState fun st =>
                          if st.hasError then st else
                          (symbolFn "::" c st).bindState fun st =>
                            if st.hasError then st else
                            st.popSyntax -- keep just `ident`
                      let noCustomCtor : ParserFn := fun _ st =>
                        st.pushSyntax (Syntax.mkNullNode #[])
                      (tryOrElseFn customCtorAttempt noCustomCtor ctx s).bindState fun s =>
                        -- Check if this is an inductive-style `class` with `| ctor` branches or field list
                        bindPeek ctx s fun next? s =>
                          match next? with
                          | some (.atom _ "|") =>
                            manyFn ctorDeclFn ctx s
                          | _ =>
                            manyFn structFieldDeclFn ctx s
                  | _ =>
                    let s := s.pushSyntax (Syntax.mkNullNode #[])
                    s.pushSyntax (Syntax.mkNullNode #[])
                sAfterBody.bindState fun s =>
                (optDerivingFn ctx s).bindState fun s =>
                  s.mkNode kind iniSz

/-- Parse a single top-level command, structurally recursive on `fuel : Nat` (for `mutual ... end`). -/
def commandStep : Nat → ParserFn
  | 0 => fun _ s => s.mkUnexpectedError "parser fuel exhausted in command"
  | fuel + 1 => fun ctx s =>
    bindPeek ctx s fun tok? s =>
      match tok? with
      | none => s.mkEOIError ["command"]
      | some (.atom _ kw) =>
        match kw with
        | "import" =>
          let iniSz := s.stackSize
          (symbolFn "import" ctx s).bindState fun s =>
            bindPeek ctx s fun next? s =>
              match next? with
              | some (.node _ k _) =>
                if k == SyntaxKind.hashRef then
                  (hashRefFn ctx s).bindState fun s =>
                    s.mkNode SyntaxKind.hashImport iniSz
                else
                  s.mkUnexpectedError "expected module name or #<hash> after 'import'"
              | _ =>
                (identFn ctx s).bindState fun s =>
                  if s.hasError then s else
                  -- Optional `@ #<hash>` pin on named import
                  bindPeek ctx s fun atTok? s =>
                    let sAfterAt := match atTok? with
                      | some (.atom _ "@") =>
                        (symbolFn "@" ctx s).bindState fun s =>
                          let s := s.popSyntax
                          hashRefFn ctx s
                      | _ =>
                        s.pushSyntax (Syntax.mkNullNode #[])
                    sAfterAt.bindState fun s =>
                      s.mkNode SyntaxKind.importDecl iniSz
        | "namespace" =>
          let iniSz := s.stackSize
          (symbolFn "namespace" ctx s).bindState fun s =>
          (identFn ctx s).bindState fun s =>
            s.mkNode SyntaxKind.namespaceDecl iniSz
        | "section" =>
          let iniSz := s.stackSize
          (symbolFn "section" ctx s).bindState fun s =>
          (optionalFn identFn ctx s).bindState fun s =>
            s.mkNode SyntaxKind.sectionDecl iniSz
        | "end" =>
          let iniSz := s.stackSize
          (symbolFn "end" ctx s).bindState fun s =>
          (optionalFn identFn ctx s).bindState fun s =>
            s.mkNode SyntaxKind.endDecl iniSz
        | "universe" =>
          let iniSz := s.stackSize
          (symbolFn "universe" ctx s).bindState fun s =>
          (many1Fn identFn ctx s).bindState fun s =>
            s.mkNode SyntaxKind.universeDecl iniSz
        | "variable" =>
          let iniSz := s.stackSize
          (symbolFn "variable" ctx s).bindState fun s =>
          (many1Fn (bracketedBinderFn termFn) ctx s).bindState fun s =>
            s.mkNode SyntaxKind.variableDecl iniSz
        | "open" =>
          let iniSz := s.stackSize
          (symbolFn "open" ctx s).bindState fun s =>
          (many1Fn identFn ctx s).bindState fun s =>
          (optionalFn (fun c st =>
            (symbolFn "(" c st).bindState fun st =>
            (many1Fn identFn c st).bindState fun st =>
              symbolFn ")" c st) ctx s).bindState fun s =>
            s.mkNode SyntaxKind.openDecl iniSz
        | "mutual" =>
          let iniSz := s.stackSize
          (symbolFn "mutual" ctx s).bindState fun s =>
            let notEnd : ParserFn := fun c st =>
              bindPeek c st fun t? st =>
                match t? with
                | some (.atom _ "end") | none => st.mkUnexpectedError "end of mutual block"
                | _ => commandStep fuel c st
            (many1Fn notEnd ctx s).bindState fun s =>
            (symbolFn "end" ctx s).bindState fun s =>
              s.mkNode SyntaxKind.mutualDecl iniSz
        | _ =>
          -- Declaration with optional modifiers (`private`, `protected`, `noncomputable`, etc.)
          (declModifiersFn ctx s).bindState fun s =>
            bindPeek ctx s fun declTok? s =>
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
          (nonReservedSymbolFn "map" ctx s).bindState fun s =>
          (identFn ctx s).bindState fun s =>
          (symbolFn ":=" ctx s).bindState fun s =>
          (hashRefFn ctx s).bindState fun s =>
            s.mkNode SyntaxKind.buildMapDecl iniSz
        else if word == "infixl" || word == "infixr" || word == "infix" then
          let iniSz := s.stackSize
          (tokenFn ctx s).bindState fun s =>
          (optionalFn (seqFn (symbolFn ":") numLitFn) ctx s).bindState fun s =>
          (strLitFn ctx s).bindState fun s =>
          (orelseFn (symbolFn "=>") (symbolFn "↦") ctx s).bindState fun s =>
          (identFn ctx s).bindState fun s =>
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

/-- Loop parsing top-level commands until EOI, accumulating `revCmds : List Ix.Syntax` in $O(1)$
    per command (avoiding $O(N^2)$ `Array.push` / `List.concat` in the kernel) and updating
    `IxParserEnv` when notation commands occur. -/
def parseModuleLoop (inputCtx : InputContext) (env : IxParserEnv) (s : ParserState)
    (revCmds : List Ix.Syntax) : Nat → Except String (Ix.Syntax × IxParserEnv)
  | 0 => .error "parser fuel exhausted in module loop"
  | fuel + 1 =>
    s.bindState fun s =>
      let ctx : IxParserContext := { inputCtx, env, prec := 0 }
      if atEOI ctx s then
        .ok (Syntax.mkNode SyntaxKind.moduleKind (Array.mk revCmds.reverse), env)
      else
        let iniSz := s.stackSize
        (commandFn ctx s).bindState fun s' =>
          match s'.errorMsg with
          | some err => .error (ParserError.toString inputCtx err)
          | none =>
            let cmd := s'.stxStack.back
            let env' := updateParserEnvFromCommand env cmd
            let sClean := s'.shrinkStack iniSz
            parseModuleLoop inputCtx env' sClean (cmd :: revCmds) fuel

/-- Parse a complete `.ix` / `.lean` source string into a `SyntaxKind.moduleKind` AST
    and the resulting `IxParserEnv`. 100% pure and deterministic (zero `IO`). -/
def parseModuleWithEnv (input : String) (fileName : String := "<input>")
    (env : IxParserEnv := defaultParserEnv) : Except String (Ix.Syntax × IxParserEnv) :=
  let inputCtx := InputContext.mkInputContext input fileName
  parseModuleLoop inputCtx env {} [] (inputCtx.charCount + 16)

/-- Parse a complete `.ix` / `.lean` source string into an `Ix.Syntax` tree. -/
def parseModule (input : String) (fileName : String := "<input>")
    (env : IxParserEnv := defaultParserEnv) : Except String Ix.Syntax := do
  let (stx, _) ← parseModuleWithEnv input fileName env
  return stx

end Ix.Frontend.Parser
