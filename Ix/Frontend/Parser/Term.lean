/-
  Ix.Frontend.Parser.Term: Pure, total, fuel-bounded Pratt expression, binder,
  substructural contract (`0`, `1`, `&`, `!`, `~`, `let borrow`), universe level,
  and tactic parser for the Ix Frontend.

  Every recursive grammar production is structurally recursive on `fuel : Nat`
  (compiled directly to `Nat.rec`, with zero `WellFounded.fix` or `partial`).
-/
module

public import Ix.Frontend.Parser.Basic

@[expose] public section

namespace Ix.Frontend.Parser

/-! ## Precedence Constants & Default Parser Environment -/

def maxPrec   : Nat := 1024
def argPrec   : Nat := 1023
def leadPrec  : Nat := 1022
def arrowPrec : Nat := 25

/-- All punctuation and operator tokens recognized by the default Ix lexer. -/
def defaultTokenSymbols : List String :=
  ["(", ")", "{", "}", "[", "]", "⦃", "⦄", "{{", "}}", "⟨", "⟩",
   ":=", "::", ":", ";", ",", ".", "..", "|", "@", "_",
   "→", "->", "←", "<-", "↔", "<->", "↦", "=>", "∀", "λ",
   "+", "-", "*", "/", "%", "^", "++",
   "==", "!=", "≠", "<=", "≤", "<", ">=", "≥", ">", "=",
   "&&", "||", "∧", "/\\", "∨", "\\/", "¬",
   "|>", "<|", "$",
   "!", "~", "&", ".{"]

/-- Reserved keywords that cannot be parsed as plain identifiers unless escaped with `«...»`. -/
def defaultKeywords : List String :=
  ["def", "abbrev", "theorem", "lemma", "axiom", "opaque", "instance",
   "inductive", "structure", "class", "where", "extending", "extends", "deriving",
   "mutual", "end", "namespace", "section", "open", "export", "variable", "universe",
   "import", "private", "protected", "noncomputable", "partial", "unsafe",
   "fun", "forall", "let", "have", "in", "if", "then", "else", "match", "with",
   "by", "Prop", "Type", "Sort", "sorry"]

/-- Builtin binary infix operators with their precedences and associativities. -/
def defaultOperators : List OperatorSpec :=
  [ { symbol := "^",   kind := SyntaxKind.binOpTerm, fixity := .infixr, prec := 80, targetFn := some (Name.mkStr2 "HPow" "hPow") }
  , { symbol := "*",   kind := SyntaxKind.binOpTerm, fixity := .infixl, prec := 70, targetFn := some (Name.mkStr2 "HMul" "hMul") }
  , { symbol := "/",   kind := SyntaxKind.binOpTerm, fixity := .infixl, prec := 70, targetFn := some (Name.mkStr2 "HDiv" "hDiv") }
  , { symbol := "%",   kind := SyntaxKind.binOpTerm, fixity := .infixl, prec := 70, targetFn := some (Name.mkStr2 "HMod" "hMod") }
  , { symbol := "::",  kind := SyntaxKind.binOpTerm, fixity := .infixr, prec := 67, targetFn := some (Name.mkStr2 "List" "cons") }
  , { symbol := "+",   kind := SyntaxKind.binOpTerm, fixity := .infixl, prec := 65, targetFn := some (Name.mkStr2 "HAdd" "hAdd") }
  , { symbol := "-",   kind := SyntaxKind.binOpTerm, fixity := .infixl, prec := 65, targetFn := some (Name.mkStr2 "HSub" "hSub") }
  , { symbol := "++",  kind := SyntaxKind.binOpTerm, fixity := .infixl, prec := 65, targetFn := some (Name.mkStr2 "HAppend" "hAppend") }
  , { symbol := "==",  kind := SyntaxKind.binOpTerm, fixity := .infixn, prec := 50, targetFn := some (Name.mkStr2 "BEq" "beq") }
  , { symbol := "!=",  kind := SyntaxKind.binOpTerm, fixity := .infixn, prec := 50, targetFn := some (Name.simple "bne") }
  , { symbol := "≠",   kind := SyntaxKind.binOpTerm, fixity := .infixn, prec := 50, targetFn := some (Name.simple "Ne") }
  , { symbol := "=",   kind := SyntaxKind.binOpTerm, fixity := .infixn, prec := 50, targetFn := some (Name.simple "Eq") }
  , { symbol := "<=",  kind := SyntaxKind.binOpTerm, fixity := .infixn, prec := 50, targetFn := some (Name.mkStr2 "LE" "le") }
  , { symbol := "≤",   kind := SyntaxKind.binOpTerm, fixity := .infixn, prec := 50, targetFn := some (Name.mkStr2 "LE" "le") }
  , { symbol := "<",   kind := SyntaxKind.binOpTerm, fixity := .infixn, prec := 50, targetFn := some (Name.mkStr2 "LT" "lt") }
  , { symbol := ">=",  kind := SyntaxKind.binOpTerm, fixity := .infixn, prec := 50, targetFn := some (Name.mkStr2 "GE" "ge") }
  , { symbol := "≥",   kind := SyntaxKind.binOpTerm, fixity := .infixn, prec := 50, targetFn := some (Name.mkStr2 "GE" "ge") }
  , { symbol := ">",   kind := SyntaxKind.binOpTerm, fixity := .infixn, prec := 50, targetFn := some (Name.mkStr2 "GT" "gt") }
  , { symbol := "&&",  kind := SyntaxKind.binOpTerm, fixity := .infixr, prec := 35, targetFn := some (Name.simple "and") }
  , { symbol := "∧",   kind := SyntaxKind.binOpTerm, fixity := .infixr, prec := 35, targetFn := some (Name.simple "And") }
  , { symbol := "/\\", kind := SyntaxKind.binOpTerm, fixity := .infixr, prec := 35, targetFn := some (Name.simple "And") }
  , { symbol := "||",  kind := SyntaxKind.binOpTerm, fixity := .infixr, prec := 30, targetFn := some (Name.simple "or") }
  , { symbol := "∨",   kind := SyntaxKind.binOpTerm, fixity := .infixr, prec := 30, targetFn := some (Name.simple "Or") }
  , { symbol := "\\/", kind := SyntaxKind.binOpTerm, fixity := .infixr, prec := 30, targetFn := some (Name.simple "Or") }
  , { symbol := "↔",   kind := SyntaxKind.binOpTerm, fixity := .infixr, prec := 20, targetFn := some (Name.simple "Iff") }
  , { symbol := "<->", kind := SyntaxKind.binOpTerm, fixity := .infixr, prec := 20, targetFn := some (Name.simple "Iff") }
  , { symbol := "|>",  kind := SyntaxKind.binOpTerm, fixity := .infixl, prec := 10, targetFn := none }
  , { symbol := "<|",  kind := SyntaxKind.binOpTerm, fixity := .infixr, prec := 10, targetFn := none }
  , { symbol := "$",   kind := SyntaxKind.binOpTerm, fixity := .infixr, prec := 10, targetFn := none }
  ]

/-- Build the default `IxParserEnv` with all core tokens, keywords, and operators. -/
def defaultParserEnv : IxParserEnv :=
  let tokens := Trie.ofSymbols defaultTokenSymbols
  let keywords := defaultKeywords.foldl (fun t kw => t.insert kw true) Trie.empty
  { tokens, keywords, operators := defaultOperators }

/-- Register a new token and optional operator spec in `IxParserEnv`. -/
def IxParserEnv.addToken (env : IxParserEnv) (sym : String) : IxParserEnv :=
  { env with tokens := env.tokens.insert sym sym }

def IxParserEnv.addOperator (env : IxParserEnv) (op : OperatorSpec) : IxParserEnv :=
  let env := env.addToken op.symbol
  { env with operators := op :: env.operators }

/-! ## Universe Level Parser (`levelFn`) -/

/-- Parse an atomic universe level: numeric literal, identifier, or `( level )`. -/
def levelAtomFn (levelRec : ParserFn) : ParserFn := fun ctx s =>
  let (tok?, s) := peekToken ctx s
  match tok? with
  | some (.node _ k #[.atom _ _]) =>
    if k == SyntaxKind.numLit then
      tokenFn ctx s
    else
      s.mkUnexpectedError "expected universe level"
  | some (.ident ..) =>
    tokenFn ctx s
  | some (.atom _ "(") =>
    let s := symbolFn "(" ctx s
    if s.hasError then s else
    let iniSz := s.stackSize
    let s := levelRec { ctx with prec := 0 } s
    if s.hasError then s else
    let lvlStx := s.stxStack.back
    let s := symbolFn ")" ctx s
    if s.hasError then s else
    let s := s.shrinkStack (iniSz - 1)
    s.pushSyntax lvlStx
  | _ =>
    s.mkUnexpectedError "expected universe level"

/-- Parse optional `+ k` universe level offset. -/
def levelTrailingAddFn : ParserFn := fun ctx s =>
  let (tok?, s) := peekToken ctx s
  match tok? with
  | some (.atom _ "+") =>
    let iniSz := s.stackSize
    let s := symbolFn "+" ctx s
    let s := numLitFn ctx s
    if s.hasError then s
    else s.mkTrailingNode SyntaxKind.levelAdd iniSz 65
  | _ => s

/-- Parse a universe level expression (`0`, `u`, `u + 1`, `max u v`, `imax u v`),
    structurally recursive on `fuel : Nat`. -/
def levelStep : Nat → ParserFn
  | 0 => fun _ s => s.mkUnexpectedError "parser fuel exhausted in universe level"
  | fuel + 1 => fun ctx s =>
    let atomWithAdd : ParserFn := fun c st =>
      let st := levelAtomFn (levelStep fuel) c st
      if st.hasError then st else levelTrailingAddFn c st
    let (tok?, s) := peekToken ctx s
    match tok? with
    | some (.ident _ _ (.str (.anonymous _) "max" _) _) =>
      let iniSz := s.stackSize
      let s := tokenFn ctx s
      let s := many1Fn atomWithAdd ctx s
      s.mkNode SyntaxKind.levelMax iniSz
    | some (.ident _ _ (.str (.anonymous _) "imax" _) _) =>
      let iniSz := s.stackSize
      let s := tokenFn ctx s
      let s := many1Fn atomWithAdd ctx s
      s.mkNode SyntaxKind.levelIMax iniSz
    | _ =>
      atomWithAdd ctx s

def levelFn : ParserFn := levelStep 64

/-- Parse optional `.{u, v}` universe level arguments on an identifier. -/
def optUnivArgsFn : ParserFn := fun ctx s =>
  let (tok?, s) := peekToken ctx s
  match tok? with
  | some (.atom _ ".{") =>
    let iniSz := s.stackSize
    let s := symbolFn ".{" ctx s
    let s := sepBy1Fn levelFn (symbolFn ",") false ctx s
    let s := symbolFn "}" ctx s
    if s.hasError then s else
    let lvls := s.stxStack.getD (iniSz + 1)
    let s := s.shrinkStack iniSz
    s.pushSyntax lvls
  | _ =>
    s.pushSyntax (Syntax.mkNullNode #[])

/-! ## Substructural Contract Modifiers (`0`, `1`, `&`, `!`, `~`) -/

/-- Parse a single usage modifier (`0`, `1`, `&`) if present at the current position. -/
def tryUsageModifierFn : ParserFn := fun ctx s =>
  let iniSz := s.stackSize
  let iniPos := s.pos
  let s' := tokenFn ctx s
  if s'.hasError then
    s'.restore iniSz iniPos
  else
    match s'.stxStack.back with
    | .node info k #[.atom _ v] =>
      if k == SyntaxKind.numLit && (v == "0" || v == "1") then
        let s' := s'.popSyntax
        s'.pushSyntax (Syntax.mkAtom info v)
      else
        s'.restore iniSz iniPos
    | .atom _ "&" => s'
    | _ => s'.restore iniSz iniPos

/-- Parse zero, one, or two value modifiers (`!`, `~`) in any order. -/
def valueModifiersLoop (ctx : IxParserContext) (s : ParserState) : Nat → ParserState
  | 0 => s
  | fuel + 1 =>
    let (tok?, s) := peekToken ctx s
    match tok? with
    | some (.atom _ "!") | some (.atom _ "~") =>
      let s := tokenFn ctx s
      valueModifiersLoop ctx s fuel
    | _ => s

/-- Parse zero to three binder modifiers (`0`, `1`, `&`, `!`, `~`) in any order. -/
def binderModifiersLoop (ctx : IxParserContext) (s : ParserState) : Nat → ParserState
  | 0 => s
  | fuel + 1 =>
    let (tok?, s) := peekToken ctx s
    match tok? with
    | some (.atom _ "!") | some (.atom _ "~") | some (.atom _ "&") =>
      let s := tokenFn ctx s
      binderModifiersLoop ctx s fuel
    | some (.node info k #[.atom _ v]) =>
      if k == SyntaxKind.numLit && (v == "0" || v == "1") then
        let s := tokenFn ctx s
        let s := s.popSyntax
        let s := s.pushSyntax (Syntax.mkAtom info v)
        binderModifiersLoop ctx s fuel
      else
        s
    | _ => s

/-- Parse an optional binder prefix (`0`, `1`, `&`, `!`, `~` in any order)
    into a `SyntaxKind.binderPrefix` node. -/
def binderPrefixFn : ParserFn := fun ctx s =>
  let iniSz := s.stackSize
  let s := binderModifiersLoop ctx s 3
  s.mkNode SyntaxKind.binderPrefix iniSz

/-- Parse an optional value contract prefix (`!`, `~`) on a domain or arrow return type
    into a `SyntaxKind.valuePrefix` node. -/
def valuePrefixFn : ParserFn := fun ctx s =>
  let iniSz := s.stackSize
  let s := valueModifiersLoop ctx s 2
  s.mkNode SyntaxKind.valuePrefix iniSz

/-- Decode a `SyntaxKind.binderPrefix` or `SyntaxKind.valuePrefix` syntax node
    into a `ParsedBinderContract`. -/
def decodeContractPrefix (stx : Ix.Syntax) : ParsedBinderContract :=
  (Syntax.getArgs stx).foldl (fun acc arg =>
    match Syntax.getAtomVal arg with
    | "0" => { acc with uses := some .erased }
    | "1" => { acc with uses := some .linear }
    | "&" => { acc with uses := some .affine }
    | "!" => { acc with owned := some .unique }
    | "~" => { acc with locality := some .local }
    | _   => acc) {}

/-- Merge two `ParsedBinderContract`s (e.g., binder-level prefix and domain-type prefix). -/
def mergeParsedContracts (a b : ParsedBinderContract) : ParsedBinderContract :=
  { uses     := b.uses.orElse (fun _ => a.uses)
    owned    := b.owned.orElse (fun _ => a.owned)
    locality := b.locality.orElse (fun _ => a.locality) }

/-! ## Binders, Tactics, and Pratt Expression Grammar -/

/-- Parse an identifier or `_` binder name. -/
def binderIdentFn : ParserFn :=
  orelseFn identFn (symbolFn "_")

/-- Parse one or more binder names (`x y _`). -/
def binderIdentsFn : ParserFn :=
  many1Fn binderIdentFn

/-- Look up a binary operator spec matching `sym` at or above `minPrec`. -/
def findInfixOp? (env : IxParserEnv) (sym : String) (minPrec : Nat) : Option OperatorSpec :=
  env.operators.find? fun op =>
    op.symbol == sym && op.prec ≥ minPrec &&
    (op.fixity == .infixl || op.fixity == .infixr || op.fixity == .infixn)

/-- Check if a token can start a function argument in juxtaposition `f a`. -/
def canStartArg (env : IxParserEnv) : Ix.Syntax → Bool
  | .ident .. => true
  | .node _ k _ =>
    k == SyntaxKind.numLit || k == SyntaxKind.strLit ||
    k == SyntaxKind.charLit || k == SyntaxKind.hashRef
  | .atom _ sym =>
    sym == "(" || sym == "⟨" || sym == "[" || sym == "{" ||
    sym == "@" || sym == "_" || sym == "Prop" || sym == "Type" ||
    sym == "Sort" || sym == "true" || sym == "false" || sym == "sorry" ||
    !(isKeyword env sym || sym == ")" || sym == "}" || sym == "]" || sym == "⦄" ||
      sym == "}}" || sym == "⟩" || sym == ":" || sym == ":=" || sym == ";" ||
      sym == "," || sym == "|" || sym == "=>" || sym == "↦" || sym == "→" ||
      sym == "->" || sym == "in" || sym == "then" || sym == "else" || sym == "with" ||
      sym == "where" || sym == "end" ||
      (env.operators.any fun op => op.symbol == sym))
  | .missing => false

/-- Parse an explicit binder `(0 x y : !A)` or `(x : A)` or `(x)`. -/
def explicitBinderFn (termRec : ParserFn) : ParserFn := fun ctx s =>
  s.bindState fun s =>
    let iniSz := s.stackSize
    (symbolFn "(" ctx s).bindState fun s =>
      if s.hasError then s else
      (binderPrefixFn ctx s).bindState fun s =>
      (binderIdentsFn ctx s).bindState fun s =>
        if s.hasError then s else
        let (tok?, s) := peekToken ctx s
        let sAfterTy := match tok? with
          | some (.atom _ ":") =>
            (symbolFn ":" ctx s).bindState fun s =>
            (valuePrefixFn ctx s).bindState fun s =>
              termRec { ctx with prec := 0 } s
          | _ =>
            let s := s.pushSyntax (Syntax.mkNode SyntaxKind.valuePrefix #[])
            s.pushSyntax (Syntax.mkNullNode #[])
        sAfterTy.bindState fun s =>
          if s.hasError then s else
          (symbolFn ")" ctx s).bindState fun s =>
            if s.hasError then s else
            let bPref := s.stxStack.getD (iniSz + 1)
            let ids   := s.stxStack.getD (iniSz + 2)
            let vPref := if s.stackSize == iniSz + 7 then s.stxStack.getD (iniSz + 4) else s.stxStack.getD (iniSz + 3)
            let ty    := if s.stackSize == iniSz + 7 then s.stxStack.getD (iniSz + 5) else s.stxStack.getD (iniSz + 4)
            let s := s.shrinkStack iniSz
            s.pushSyntax (Syntax.mkNode SyntaxKind.explicitBinder #[bPref, ids, vPref, ty])

/-- Parse an implicit binder `{0 α β : Type}` or `{α β}`. -/
def implicitBinderFn (termRec : ParserFn) : ParserFn := fun ctx s =>
  let iniSz := s.stackSize
  let s := symbolFn "{" ctx s
  if s.hasError then s else
  let s := binderPrefixFn ctx s
  let s := binderIdentsFn ctx s
  if s.hasError then s else
  let (tok?, s) := peekToken ctx s
  let s := match tok? with
    | some (.atom _ ":") =>
      let s := symbolFn ":" ctx s
      let s := valuePrefixFn ctx s
      termRec { ctx with prec := 0 } s
    | _ =>
      let s := s.pushSyntax (Syntax.mkNode SyntaxKind.valuePrefix #[])
      s.pushSyntax (Syntax.mkNullNode #[])
  if s.hasError then s else
  let s := symbolFn "}" ctx s
  if s.hasError then s else
  let bPref := s.stxStack.getD (iniSz + 1)
  let ids   := s.stxStack.getD (iniSz + 2)
  let vPref := if s.stackSize == iniSz + 7 then s.stxStack.getD (iniSz + 4) else s.stxStack.getD (iniSz + 3)
  let ty    := if s.stackSize == iniSz + 7 then s.stxStack.getD (iniSz + 5) else s.stxStack.getD (iniSz + 4)
  let s := s.shrinkStack iniSz
  s.pushSyntax (Syntax.mkNode SyntaxKind.implicitBinder #[bPref, ids, vPref, ty])

/-- Parse a strict-implicit binder `⦃x : A⦄` or `{{x : A}}`. -/
def strictImplicitBinderFn (termRec : ParserFn) : ParserFn := fun ctx s =>
  let iniSz := s.stackSize
  let (tok?, s) := peekToken ctx s
  let closeSym := match tok? with
    | some (.atom _ "{{") => "}}"
    | _ => "⦄"
  let openSym := if closeSym == "}}" then "{{" else "⦃"
  let s := symbolFn openSym ctx s
  if s.hasError then s else
  let s := binderPrefixFn ctx s
  let s := binderIdentsFn ctx s
  if s.hasError then s else
  let (tok?, s) := peekToken ctx s
  let s := match tok? with
    | some (.atom _ ":") =>
      let s := symbolFn ":" ctx s
      let s := valuePrefixFn ctx s
      termRec { ctx with prec := 0 } s
    | _ =>
      let s := s.pushSyntax (Syntax.mkNode SyntaxKind.valuePrefix #[])
      s.pushSyntax (Syntax.mkNullNode #[])
  if s.hasError then s else
  let s := symbolFn closeSym ctx s
  if s.hasError then s else
  let bPref := s.stxStack.getD (iniSz + 1)
  let ids   := s.stxStack.getD (iniSz + 2)
  let vPref := if s.stackSize == iniSz + 7 then s.stxStack.getD (iniSz + 4) else s.stxStack.getD (iniSz + 3)
  let ty    := if s.stackSize == iniSz + 7 then s.stxStack.getD (iniSz + 5) else s.stxStack.getD (iniSz + 4)
  let s := s.shrinkStack iniSz
  s.pushSyntax (Syntax.mkNode SyntaxKind.strictImplicitBinder #[bPref, ids, vPref, ty])

/-- Parse an instance-implicit binder `[inst : Add α]` or `[Add α]`. -/
def instBinderFn (termRec : ParserFn) : ParserFn := fun ctx s =>
  let iniSz := s.stackSize
  let s := symbolFn "[" ctx s
  if s.hasError then s else
  let namedAttempt : ParserFn := fun c st =>
    let st := binderPrefixFn c st
    let st := binderIdentFn c st
    if st.hasError then st else
    let st := symbolFn ":" c st
    if st.hasError then st else
    let st := valuePrefixFn c st
    termRec { c with prec := 0 } st
  let anonAttempt : ParserFn := fun c st =>
    let st := st.pushSyntax (Syntax.mkNode SyntaxKind.binderPrefix #[])
    let st := st.pushSyntax (Syntax.mkSimpleIdent Name.mkAnon)
    let st := st.pushSyntax (Syntax.mkNode SyntaxKind.valuePrefix #[])
    termRec { c with prec := 0 } st
  let s := tryOrElseFn namedAttempt anonAttempt ctx s
  if s.hasError then s else
  let s := symbolFn "]" ctx s
  if s.hasError then s else
  let bPref := s.stxStack.getD (iniSz + 1)
  let idStx := s.stxStack.getD (iniSz + 2)
  let (vPref, ty) :=
    if s.stackSize == iniSz + 7 then
      (s.stxStack.getD (iniSz + 4), s.stxStack.getD (iniSz + 5))
    else
      (s.stxStack.getD (iniSz + 3), s.stxStack.getD (iniSz + 4))
  let s := s.shrinkStack iniSz
  s.pushSyntax (Syntax.mkNode SyntaxKind.instBinder #[bPref, Syntax.mkNullNode #[idStx], vPref, ty])

/-- Parse any bracketed binder `(...)`, `{...}`, `⦃...⦄`, `[...]`. -/
def bracketedBinderFn (termRec : ParserFn) : ParserFn := fun ctx s =>
  let (tok?, s) := peekToken ctx s
  match tok? with
  | some (.atom _ "(") => explicitBinderFn termRec ctx s
  | some (.atom _ "{") => implicitBinderFn termRec ctx s
  | some (.atom _ "⦃") | some (.atom _ "{{") => strictImplicitBinderFn termRec ctx s
  | some (.atom _ "[") => instBinderFn termRec ctx s
  | _ => s.mkUnexpectedError "expected binder"

/-- Parse a `fun` / `forall` binder: either a bracketed binder or an unparenthesized identifier `x`. -/
def simpleOrBracketedBinderFn (termRec : ParserFn) : ParserFn := fun ctx s =>
  let (tok?, s) := peekToken ctx s
  match tok? with
  | some (.atom _ "(") | some (.atom _ "{") | some (.atom _ "⦃")
  | some (.atom _ "{{") | some (.atom _ "[") =>
    bracketedBinderFn termRec ctx s
  | _ =>
    let iniSz := s.stackSize
    let s := binderIdentFn ctx s
    if s.hasError then s else
    let idStx := s.stxStack.back
    let s := s.shrinkStack iniSz
    let emptyPref := Syntax.mkNode SyntaxKind.binderPrefix #[]
    let emptyVPref := Syntax.mkNode SyntaxKind.valuePrefix #[]
    s.pushSyntax (Syntax.mkNode SyntaxKind.explicitBinder
      #[emptyPref, Syntax.mkNullNode #[idStx], emptyVPref, Syntax.mkNullNode #[]])

/-- Parse a tactic sequence, structurally recursive on `fuel : Nat`. -/
def tacticSeqStep (termRec : ParserFn) : Nat → ParserFn
  | 0 => fun _ s => s.mkUnexpectedError "parser fuel exhausted in tactic"
  | fuel + 1 =>
    let term0 := withPrecFn 0 termRec
    let termArg := withPrecFn argPrec termRec
    let tacticAlt : ParserFn := fun ctx s =>
      let iniSz := s.stackSize
      let s := symbolFn "|" ctx s
      if s.hasError then s else
      let s := identFn ctx s
      let s := manyFn binderIdentFn ctx s
      let s := orelseFn (symbolFn "=>") (symbolFn "↦") ctx s
      let s := tacticSeqStep termRec fuel ctx s
      s.mkNode SyntaxKind.tacticAlt iniSz
    let oneTactic : ParserFn := fun ctx s =>
      let (tok?, s) := peekToken ctx s
      match tok? with
      | some (.ident _ _ (.str (.anonymous _) kw _) _) | some (.atom _ kw) =>
        let iniSz := s.stackSize
        match kw with
        | "intro" | "intros" =>
          let s := tokenFn ctx s
          let sameLineBinderIdent : ParserFn := fun c st =>
            let (t?, st) := peekToken c st
            match t? with
            | some tok =>
              if hasLeadingNewline tok then st.mkUnexpectedError "newline after intro"
              else binderIdentFn c st
            | none => st.mkUnexpectedError "end of intro"
          let s := manyFn sameLineBinderIdent ctx s
          s.mkNode SyntaxKind.tacticIntro iniSz
        | "exact" =>
          let s := tokenFn ctx s
          let s := term0 ctx s
          s.mkNode SyntaxKind.tacticExact iniSz
        | "apply" =>
          let s := tokenFn ctx s
          let s := term0 ctx s
          s.mkNode SyntaxKind.tacticApply iniSz
        | "refine" =>
          let s := tokenFn ctx s
          let s := term0 ctx s
          s.mkNode SyntaxKind.tacticRefine iniSz
        | "rfl" =>
          let s := tokenFn ctx s
          s.mkNode SyntaxKind.tacticRfl iniSz
        | "decide" =>
          let s := tokenFn ctx s
          s.mkNode SyntaxKind.tacticDecide iniSz
        | "assumption" =>
          let s := tokenFn ctx s
          s.mkNode SyntaxKind.tacticAssumption iniSz
        | "constructor" =>
          let s := tokenFn ctx s
          s.mkNode SyntaxKind.tacticConstructor iniSz
        | "sorry" =>
          let s := tokenFn ctx s
          s.mkNode SyntaxKind.tacticSorry iniSz
        | "change" =>
          let s := tokenFn ctx s
          let s := term0 ctx s
          s.mkNode SyntaxKind.tacticChange iniSz
        | "rw" | "rewrite" =>
          let s := tokenFn ctx s
          let s := symbolFn "[" ctx s
          let rwRule : ParserFn := fun c st =>
            let rSz := st.stackSize
            let st := optionalFn (orelseFn (symbolFn "←") (symbolFn "<-")) c st
            let st := term0 c st
            st.mkNode SyntaxKind.tacticRwRule rSz
          let s := sepBy1Fn rwRule (symbolFn ",") false ctx s
          let s := symbolFn "]" ctx s
          s.mkNode SyntaxKind.tacticRw iniSz
        | "simp" =>
          let s := tokenFn ctx s
          let s := optionalFn (fun c st =>
            let st := symbolFn "[" c st
            let st := sepByFn term0 (symbolFn ",") false c st
            symbolFn "]" c st) ctx s
          s.mkNode SyntaxKind.tacticSimp iniSz
        | "have" =>
          let s := tokenFn ctx s
          let s := binderIdentFn ctx s
          let s := symbolFn ":" ctx s
          let s := term0 ctx s
          let s := symbolFn ":=" ctx s
          let s := term0 ctx s
          s.mkNode SyntaxKind.tacticHave iniSz
        | "let" =>
          let s := tokenFn ctx s
          let s := binderIdentFn ctx s
          let s := optionalFn (seqFn (symbolFn ":") term0) ctx s
          let s := symbolFn ":=" ctx s
          let s := term0 ctx s
          s.mkNode SyntaxKind.tacticLet iniSz
        | "cases" =>
          let s := tokenFn ctx s
          let s := termArg ctx s
          let s := optionalFn (seqFn (symbolFn "with") (manyFn tacticAlt)) ctx s
          s.mkNode SyntaxKind.tacticCases iniSz
        | "induction" =>
          let s := tokenFn ctx s
          let s := termArg ctx s
          let s := optionalFn (seqFn (symbolFn "with") (manyFn tacticAlt)) ctx s
          s.mkNode SyntaxKind.tacticInduction iniSz
        | _ =>
          s.mkUnexpectedError s!"expected tactic, got '{kw}'"
      | _ =>
        s.mkUnexpectedError "expected tactic"
    fun ctx s =>
      let iniSz := s.stackSize
      let s := oneTactic ctx s
      if s.hasError then s else
      let s := manyLoop (fun c st =>
        let st := optionalFn (symbolFn ";") c st
        let st := st.popSyntax
        oneTactic c st) ctx s (ctx.inputCtx.size - s.pos + 1)
      s.mkNode SyntaxKind.tacticSeq iniSz

/-- Parse a `| pat1, pat2 => rhs` branch of a `match` expression. -/
def matchAltFn (termRec : ParserFn) : ParserFn := fun ctx s =>
  let term0 := withPrecFn 0 termRec
  let iniSz := s.stackSize
  let s := symbolFn "|" ctx s
  if s.hasError then s else
  let s := sepBy1Fn term0 (symbolFn ",") false ctx s
  if s.hasError then s else
  let s := orelseFn (symbolFn "=>") (symbolFn "↦") ctx s
  if s.hasError then s else
  let s := term0 ctx s
  s.mkNode SyntaxKind.matchAlt iniSz

/-- Parse a leading expression (atoms, binders, `fun`, `forall`, `let`, `let borrow`, `if`, `match`, `by`). -/
def leadTermFn (termRec : ParserFn) (tacticFuel : Nat) : ParserFn := fun ctx s =>
  let term0 := withPrecFn 0 termRec
  let (tok?, s) := peekToken ctx s
  match tok? with
  | none => s.mkEOIError ["term"]
  -- 1. Literals & content-hash references
  | some (.node _ k _) =>
    if k == SyntaxKind.numLit || k == SyntaxKind.strLit ||
       k == SyntaxKind.charLit || k == SyntaxKind.hashRef then
      tokenFn ctx s
    else
      s.mkUnexpectedError "unexpected syntax node in term"
  -- 2. Identifiers (with optional `.{u, v}` universe levels)
  | some (.ident ..) =>
    let iniSz := s.stackSize
    let s := identFn ctx s
    let (nextTok?, s) := peekToken ctx s
    match nextTok? with
    | some (.atom _ ".{") =>
      let s := optUnivArgsFn ctx s
      s.mkNode SyntaxKind.explicitTerm iniSz
    | _ => s
  -- 3. Keywords and leading symbols
  | some (.atom _ sym) =>
    match sym with
    | "_" =>
      let iniSz := s.stackSize
      let s := symbolFn "_" ctx s
      s.mkNode SyntaxKind.holeTerm iniSz
    | "sorry" =>
      let iniSz := s.stackSize
      let s := symbolFn "sorry" ctx s
      s.mkNode SyntaxKind.sorryTerm iniSz
    | "Prop" =>
      let iniSz := s.stackSize
      let s := symbolFn "Prop" ctx s
      s.mkNode SyntaxKind.propTerm iniSz
    | "Type" =>
      let iniSz := s.stackSize
      let s := symbolFn "Type" ctx s
      let (nextTok?, s) := peekToken ctx s
      let s := match nextTok? with
        | some (.node _ k _) =>
          if k == SyntaxKind.numLit then levelFn ctx s
          else s.pushSyntax (Syntax.mkNullNode #[])
        | some (.ident ..) | some (.atom _ "(") =>
          optionalFn (withPrecFn maxPrec (levelAtomFn levelFn)) ctx s
        | _ => s.pushSyntax (Syntax.mkNullNode #[])
      s.mkNode SyntaxKind.typeTerm iniSz
    | "Sort" =>
      let iniSz := s.stackSize
      let s := symbolFn "Sort" ctx s
      let s := optionalFn (withPrecFn maxPrec (levelAtomFn levelFn)) ctx s
      s.mkNode SyntaxKind.sortTerm iniSz
    | "@" =>
      let iniSz := s.stackSize
      let s := symbolFn "@" ctx s
      let s := identFn ctx s
      let s := optUnivArgsFn ctx s
      s.mkNode SyntaxKind.explicitTerm iniSz
    | "fun" | "λ" =>
      let iniSz := s.stackSize
      let s := tokenFn ctx s
      let s := many1Fn (simpleOrBracketedBinderFn termRec) ctx s
      let s := orelseFn (symbolFn "=>") (symbolFn "↦") ctx s
      let s := term0 ctx s
      s.mkNode SyntaxKind.funTerm iniSz
    | "forall" | "∀" =>
      let iniSz := s.stackSize
      let s := tokenFn ctx s
      let s := many1Fn (simpleOrBracketedBinderFn termRec) ctx s
      if s.hasError then s else
      let (sepTok?, s) := peekToken ctx s
      match sepTok? with
      | some (.atom _ ":") =>
        -- Could be either unparenthesized typed binders `∀ a b c : T, body` OR `forall (x : A) : body`
        let s := symbolFn ":" ctx s
        let s := valuePrefixFn ctx s
        let s := term0 ctx s
        if s.hasError then s else
        let (afterTyTok?, s) := peekToken ctx s
        match afterTyTok? with
        | some (.atom _ ",") =>
          -- `∀ a b c : T, body` -> attach `T` to untyped `explicitBinder`s in `bindersNode`!
          let kwTok := s.stxStack.getD iniSz
          let bindersNode := s.stxStack.getD (iniSz + 1)
          let bVPref := s.stxStack.getD (iniSz + 3)
          let bTy := s.stxStack.getD (iniSz + 4)
          let updatedBinders := (Syntax.getArgs bindersNode).map fun b =>
            if Syntax.isOfKind b SyntaxKind.explicitBinder && Syntax.isNone (Syntax.getArg b 3) then
              Syntax.mkNode SyntaxKind.explicitBinder #[Syntax.getArg b 0, Syntax.getArg b 1, bVPref, bTy]
            else b
          let s := s.shrinkStack iniSz
          let s := s.pushSyntax kwTok
          let s := s.pushSyntax (Syntax.mkNullNode updatedBinders)
          let s := symbolFn "," ctx s
          let s := valuePrefixFn ctx s
          let s := term0 ctx s
          s.mkNode SyntaxKind.forallTerm iniSz
        | _ =>
          s.mkNode SyntaxKind.forallTerm iniSz
      | _ =>
        let s := symbolFn "," ctx s
        let s := valuePrefixFn ctx s
        let s := term0 ctx s
        s.mkNode SyntaxKind.forallTerm iniSz
    | "let" =>
      let iniSz := s.stackSize
      let s := symbolFn "let" ctx s
      let (afterLet?, s) := peekToken ctx s
      let isBorrow := match afterLet? with
        | some (.ident _ _ (.str (.anonymous _) "borrow" _) _) => true
        | _ => false
      let s := if isBorrow then nonReservedSymbolFn "borrow" ctx s else s
      let s := binderPrefixFn ctx s
      let s := binderIdentFn ctx s
      if s.hasError then s else
      let s := manyFn (simpleOrBracketedBinderFn termRec) ctx s
      let s := optionalFn (fun c st =>
        let st := symbolFn ":" c st
        if st.hasError then st else
        let st := valuePrefixFn c st
        term0 c st) ctx s
      if s.hasError then s else
      let s := symbolFn ":=" ctx s
      if s.hasError then s else
      let s := term0 ctx s
      if s.hasError then s else
      let s := optionalFn (orelseFn (symbolFn ";") (symbolFn "in")) ctx s
      let s := term0 ctx s
      s.mkNode (if isBorrow then SyntaxKind.letBorrowTerm else SyntaxKind.letTerm) iniSz
    | "have" =>
      let iniSz := s.stackSize
      let s := symbolFn "have" ctx s
      let s := binderIdentFn ctx s
      if s.hasError then s else
      let s := optionalFn (seqFn (symbolFn ":") term0) ctx s
      if s.hasError then s else
      let s := symbolFn ":=" ctx s
      if s.hasError then s else
      let s := term0 ctx s
      if s.hasError then s else
      let s := optionalFn (orelseFn (symbolFn ";") (symbolFn "in")) ctx s
      let s := term0 ctx s
      s.mkNode SyntaxKind.haveTerm iniSz
    | "if" =>
      let iniSz := s.stackSize
      let s := symbolFn "if" ctx s
      let depCondAttempt : ParserFn := fun c st =>
        let st := identFn c st
        let st := symbolFn ":" c st
        term0 c st
      let plainCondAttempt : ParserFn := fun c st =>
        let st := st.pushSyntax (Syntax.mkNullNode #[])
        term0 c st
      let s := tryOrElseFn depCondAttempt plainCondAttempt ctx s
      let s := symbolFn "then" ctx s
      let s := term0 ctx s
      let s := symbolFn "else" ctx s
      let s := term0 ctx s
      s.mkNode SyntaxKind.ifTerm iniSz
    | "match" =>
      let iniSz := s.stackSize
      let s := symbolFn "match" ctx s
      let s := sepBy1Fn term0 (symbolFn ",") false ctx s
      let s := symbolFn "with" ctx s
      let s := many1Fn (matchAltFn termRec) ctx s
      s.mkNode SyntaxKind.matchTerm iniSz
    | "by" =>
      let iniSz := s.stackSize
      let s := symbolFn "by" ctx s
      let s := tacticSeqStep termRec tacticFuel ctx s
      s.mkNode SyntaxKind.byTactic iniSz
    | "(" =>
      let depPiAttempt : ParserFn := fun c st =>
        let pSz := st.stackSize
        let st := many1Fn (bracketedBinderFn termRec) c st
        if st.hasError then st else
        let st := orelseFn (symbolFn "→") (symbolFn "->") c st
        if st.hasError then st else
        let st := valuePrefixFn c st
        let st := termRec { c with prec := arrowPrec - 1 } st
        st.mkNode SyntaxKind.forallTerm pSz
      let parenAttempt : ParserFn := fun c st =>
        let pSz := st.stackSize
        let st := symbolFn "(" c st
        if st.hasError then st else
        let (next?, st) := peekToken c st
        match next? with
        | some (.atom _ ")") =>
          let st := symbolFn ")" c st
          st.mkNode SyntaxKind.tupleTerm pSz
        | _ =>
          let st := term0 c st
          if st.hasError then st else
          let (afterFirst?, st) := peekToken c st
          match afterFirst? with
          | some (.atom _ ":") =>
            let st := symbolFn ":" c st
            let st := valuePrefixFn c st
            let st := term0 c st
            let st := symbolFn ")" c st
            st.mkNode SyntaxKind.typeAscription pSz
          | some (.atom _ ",") =>
            let st := symbolFn "," c st
            let st := sepBy1Fn term0 (symbolFn ",") true c st
            let st := symbolFn ")" c st
            st.mkNode SyntaxKind.tupleTerm pSz
          | _ =>
            let inner := st.stxStack.back
            let st := symbolFn ")" c st
            if st.hasError then st else
            let st := st.shrinkStack pSz
            st.pushSyntax inner
      tryOrElseFn depPiAttempt parenAttempt ctx s
    | "{" | "⦃" | "{{" =>
      let depPiAttempt : ParserFn := fun c st =>
        let pSz := st.stackSize
        let st := many1Fn (bracketedBinderFn termRec) c st
        if st.hasError then st else
        let st := orelseFn (symbolFn "→") (symbolFn "->") c st
        if st.hasError then st else
        let st := valuePrefixFn c st
        let st := termRec { c with prec := arrowPrec - 1 } st
        st.mkNode SyntaxKind.forallTerm pSz
      let structInstAttempt : ParserFn := fun c st =>
        let pSz := st.stackSize
        let st := symbolFn "{" c st
        if st.hasError then st else
        let withAttempt : ParserFn := fun c2 st2 =>
          let st2 := term0 c2 st2
          if st2.hasError then st2 else
          nonReservedSymbolFn "with" c2 st2
        let noWith : ParserFn := fun _ st2 =>
          st2.pushSyntax (Syntax.mkNullNode #[])
        let st := tryOrElseFn withAttempt noWith c st
        let fieldAssign : ParserFn := fun c2 st2 =>
          let fSz := st2.stackSize
          let st2 := identFn c2 st2
          let st2 := symbolFn ":=" c2 st2
          let st2 := term0 c2 st2
          st2.mkNode SyntaxKind.structFieldAssign fSz
        let st := sepByFn fieldAssign (symbolFn ",") true c st
        let st := symbolFn "}" c st
        st.mkNode SyntaxKind.structInst pSz
      tryOrElseFn depPiAttempt structInstAttempt ctx s
    | "[" =>
      let depPiAttempt : ParserFn := fun c st =>
        let pSz := st.stackSize
        let st := many1Fn (bracketedBinderFn termRec) c st
        if st.hasError then st else
        let st := orelseFn (symbolFn "→") (symbolFn "->") c st
        if st.hasError then st else
        let st := valuePrefixFn c st
        let st := termRec { c with prec := arrowPrec - 1 } st
        st.mkNode SyntaxKind.forallTerm pSz
      let listLitAttempt : ParserFn := fun c st =>
        let pSz := st.stackSize
        let st := symbolFn "[" c st
        if st.hasError then st else
        let st := sepByFn term0 (symbolFn ",") true c st
        let st := symbolFn "]" c st
        st.mkNode SyntaxKind.listLit pSz
      tryOrElseFn depPiAttempt listLitAttempt ctx s
    | "⟨" =>
      let iniSz := s.stackSize
      let s := symbolFn "⟨" ctx s
      let s := sepByFn term0 (symbolFn ",") true ctx s
      let s := symbolFn "⟩" ctx s
      s.mkNode SyntaxKind.anonCtor iniSz
    | "-" | "!" | "¬" =>
      let iniSz := s.stackSize
      let s := tokenFn ctx s
      let s := termRec { ctx with prec := leadPrec } s
      s.mkNode SyntaxKind.unaryOpTerm iniSz
    | _ =>
      s.mkUnexpectedError s!"unexpected token '{sym}' in term"
  | _ =>
    s.mkUnexpectedError "expected term"

/-- Pratt trailing loop: handles `.field` / `.0` projections, function application `f a`,
    substructural function arrows `A → !B`, and binary infix operators. -/
def trailingTermLoop (termRec : ParserFn) (ctx : IxParserContext) (s : ParserState) :
    Nat → ParserState
  | 0 => s
  | fuel + 1 =>
    if s.hasError then s else
    let (tok?, s) := peekToken ctx s
    match tok? with
    | none => s
    | some tok =>
      -- 1. Field or index projection `.field` / `.0` (tightest binding, `maxPrec`)
      if Syntax.getAtomVal tok == "." && ctx.prec < maxPrec then
        let iniSz := s.stackSize
        let s := symbolFn "." ctx s
        let s := orelseFn identFn numLitFn ctx s
        if s.hasError then s else
        let s := s.mkTrailingNode SyntaxKind.projTerm iniSz maxPrec
        trailingTermLoop termRec ctx s fuel
      -- 2. Non-dependent function arrow `A → !B` / `A -> ~B` (precedence `arrowPrec := 25`, right-assoc)
      else if (Syntax.getAtomVal tok == "→" || Syntax.getAtomVal tok == "->") && ctx.prec ≤ arrowPrec then
        let iniSz := s.stackSize
        let s := tokenFn ctx s
        let s := valuePrefixFn ctx s
        let s := termRec { ctx with prec := arrowPrec } s
        if s.hasError then s else
        let s := s.mkTrailingNode SyntaxKind.arrowTerm iniSz arrowPrec
        trailingTermLoop termRec ctx s fuel
      -- 3. Registered binary infix operator
      else
        match findInfixOp? ctx.env (Syntax.getAtomVal tok) ctx.prec with
        | some op =>
          let iniSz := s.stackSize
          let s := tokenFn ctx s
          let rhsMinPrec := match op.fixity with
            | .infixl => op.prec + 1
            | .infixr => op.prec
            | _       => op.prec + 1
          let s := termRec { ctx with prec := rhsMinPrec } s
          if s.hasError then s else
          let s := s.mkTrailingNode op.kind iniSz op.prec
          trailingTermLoop termRec ctx s fuel
        | none =>
          -- 4. Juxtaposition application `f arg` when `ctx.prec < argPrec` (on the same line)
          if ctx.prec < argPrec && !hasLeadingNewline tok && canStartArg ctx.env tok then
            let iniSz := s.stackSize
            let s := termRec { ctx with prec := argPrec } s
            if s.hasError then s else
            let s := s.mkTrailingNode SyntaxKind.appTerm iniSz argPrec
            trailingTermLoop termRec ctx s fuel
          else
            s

/-- Parse an expression at minimum precedence `ctx.prec`, structurally recursive on `fuel : Nat`. -/
def termStep : Nat → ParserFn
  | 0 => fun _ s => s.mkUnexpectedError "parser fuel exhausted in term"
  | fuel + 1 => fun ctx s =>
    let termRec := termStep fuel
    (leadTermFn termRec fuel ctx s).bindState fun s =>
      if s.hasError then s else
      let loopFuel := ctx.inputCtx.size - s.pos + 1
      trailingTermLoop termRec ctx s loopFuel

/-- Default expression parser combinator (`termStep 256`). -/
def termFn : ParserFn := termStep 256

/-- Convenience entry point: parse a standalone expression string into `Ix.Syntax`. -/
def parseTerm (input : String) (env : IxParserEnv := defaultParserEnv)
    (fuel : Nat := 256) : Except String Ix.Syntax :=
  let inputCtx := InputContext.mkInputContext input "<term>"
  let ctx : IxParserContext := { inputCtx, env, prec := 0 }
  let s := termStep fuel ctx {}
  match s.errorMsg with
  | some err => .error (ParserError.toString inputCtx err)
  | none =>
    if !atEOI ctx s then
      let err : ParserError := { pos := s.pos, unexpected := "unexpected trailing tokens" }
      .error (ParserError.toString inputCtx err)
    else
      .ok s.stxStack.back

end Ix.Frontend.Parser
