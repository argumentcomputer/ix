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

/-- Strictly fold a list of keyword strings into a `Trie Bool`. -/
def ofKeywordsLoop : Trie Bool → List String → Trie Bool
  | t, [] => t
  | t, kw :: kws =>
    match t.insert kw true with
    | .node v ch => ofKeywordsLoop (.node v ch) kws

/-- Build the default `IxParserEnv` with all core tokens, keywords, and operators. -/
def defaultParserEnv : IxParserEnv :=
  match Trie.ofSymbols defaultTokenSymbols, ofKeywordsLoop Trie.empty defaultKeywords with
  | .node tv tch, .node kv kch =>
    { tokens := .node tv tch, keywords := .node kv kch, operators := defaultOperators }

/-- Register a new token and optional operator spec in `IxParserEnv`. -/
def IxParserEnv.addToken (env : IxParserEnv) (sym : String) : IxParserEnv :=
  match env with
  | ⟨tokens, keywords, operators⟩ =>
    match tokens.insert sym sym with
    | .node tv tch => ⟨.node tv tch, keywords, operators⟩

def IxParserEnv.addOperator (env : IxParserEnv) (op : OperatorSpec) : IxParserEnv :=
  match env.addToken op.symbol with
  | ⟨tokens, keywords, operators⟩ => ⟨tokens, keywords, op :: operators⟩

/-! ## Universe Level Parser (`levelFn`) -/

/-- Parse an atomic universe level: numeric literal, identifier, or `( level )`. -/
def levelAtomFn (levelRec : ParserFn) : ParserFn := fun ctx s =>
  bindPeek ctx s fun tok? s =>
    match tok? with
    | some (.node _ k #[.atom _ _]) =>
      if k == SyntaxKind.numLit then
        tokenFn ctx s
      else
        s.mkUnexpectedError "expected universe level"
    | some (.ident ..) =>
      tokenFn ctx s
    | some (.atom _ "(") =>
      (symbolFn "(" ctx s).bindState fun s =>
        if s.hasError then s else
        let iniSz := s.stackSize
        (withPrecFn 0 levelRec ctx s).bindState fun s =>
          if s.hasError then s else
          let lvlStx := s.stxStack.back
          (symbolFn ")" ctx s).bindState fun s =>
            if s.hasError then s else
            let s := s.shrinkStack (iniSz - 1)
            s.pushSyntax lvlStx
    | _ =>
      s.mkUnexpectedError "expected universe level"

/-- Parse optional `+ k` universe level offset. -/
def levelTrailingAddFn : ParserFn := fun ctx s =>
  bindPeek ctx s fun tok? s =>
    match tok? with
    | some (.atom _ "+") =>
      let iniSz := s.stackSize
      (symbolFn "+" ctx s).bindState fun s =>
      (numLitFn ctx s).bindState fun s =>
        if s.hasError then s
        else s.mkTrailingNode SyntaxKind.levelAdd iniSz 65
    | _ => s

/-- Parse a universe level expression (`0`, `u`, `u + 1`, `max u v`, `imax u v`),
    structurally recursive on `fuel : Nat`. -/
def levelStep : Nat → ParserFn
  | 0 => fun _ s => s.mkUnexpectedError "parser fuel exhausted in universe level"
  | fuel + 1 => fun ctx s =>
    let atomWithAdd : ParserFn := fun c st =>
      (levelAtomFn (levelStep fuel) c st).bindState fun st =>
        if st.hasError then st else levelTrailingAddFn c st
    bindPeek ctx s fun tok? s =>
      match tok? with
      | some (.ident _ _ (.str (.anonymous _) "max" _) _) =>
        let iniSz := s.stackSize
        (tokenFn ctx s).bindState fun s =>
        (many1Fn atomWithAdd ctx s).bindState fun s =>
          s.mkNode SyntaxKind.levelMax iniSz
      | some (.ident _ _ (.str (.anonymous _) "imax" _) _) =>
        let iniSz := s.stackSize
        (tokenFn ctx s).bindState fun s =>
        (many1Fn atomWithAdd ctx s).bindState fun s =>
          s.mkNode SyntaxKind.levelIMax iniSz
      | _ =>
        atomWithAdd ctx s

def levelFn : ParserFn := levelStep 64

/-- Parse optional `.{u, v}` universe level arguments on an identifier. -/
def optUnivArgsFn : ParserFn := fun ctx s =>
  bindPeek ctx s fun tok? s =>
    match tok? with
    | some (.atom _ ".{") =>
      let iniSz := s.stackSize
      (symbolFn ".{" ctx s).bindState fun s =>
      (sepBy1Fn levelFn (symbolFn ",") false ctx s).bindState fun s =>
      (symbolFn "}" ctx s).bindState fun s =>
        if s.hasError then s else
        let lvls := s.stxStack.getD (iniSz + 1)
        let s := s.shrinkStack iniSz
        s.pushSyntax lvls
    | _ =>
      s.pushSyntax (Syntax.mkNullNode #[])

/-! ## Substructural Contract Modifiers (`0`, `1`, `&`, `!`, `~`) -/

/-- Parse a single usage modifier (`0`, `1`, `&`) if present at the current position. -/
def tryUsageModifierFn : ParserFn := fun ctx s =>
  s.bindState fun s =>
    let iniSz := s.stackSize
    let iniPos := s.pos
    (tokenFn ctx s).bindState fun s' =>
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
    bindPeek ctx s fun tok? s =>
      match tok? with
      | some (.atom _ "!") | some (.atom _ "~") =>
        (tokenFn ctx s).bindState fun s =>
          valueModifiersLoop ctx s fuel
      | _ => s

/-- Parse zero to three binder modifiers (`0`, `1`, `&`, `!`, `~`) in any order. -/
def binderModifiersLoop (ctx : IxParserContext) (s : ParserState) : Nat → ParserState
  | 0 => s
  | fuel + 1 =>
    bindPeek ctx s fun tok? s =>
      match tok? with
      | some (.atom _ "!") | some (.atom _ "~") | some (.atom _ "&") =>
        (tokenFn ctx s).bindState fun s =>
          binderModifiersLoop ctx s fuel
      | some (.node info k #[.atom _ v]) =>
        if k == SyntaxKind.numLit && (v == "0" || v == "1") then
          (tokenFn ctx s).bindState fun s =>
            let s := s.popSyntax
            let s := s.pushSyntax (Syntax.mkAtom info v)
            binderModifiersLoop ctx s fuel
        else
          s
      | _ => s

/-- Parse an optional binder prefix (`0`, `1`, `&`, `!`, `~` in any order)
    into a `SyntaxKind.binderPrefix` node. -/
def binderPrefixFn : ParserFn := fun ctx s =>
  s.bindState fun s =>
    let iniSz := s.stackSize
    (binderModifiersLoop ctx s 3).bindState fun s =>
      s.mkNode SyntaxKind.binderPrefix iniSz

/-- Parse an optional value contract prefix (`!`, `~`) on a domain or arrow return type
    into a `SyntaxKind.valuePrefix` node. -/
def valuePrefixFn : ParserFn := fun ctx s =>
  s.bindState fun s =>
    let iniSz := s.stackSize
    (valueModifiersLoop ctx s 2).bindState fun s =>
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
        bindPeek ctx s fun tok? s =>
          let sAfterTy := match tok? with
            | some (.atom _ ":") =>
              (symbolFn ":" ctx s).bindState fun s =>
              (valuePrefixFn ctx s).bindState fun s =>
                withPrecFn 0 termRec ctx s
            | _ =>
              let s := s.pushSyntax (Syntax.mkNode SyntaxKind.valuePrefix #[])
              s.pushSyntax (Syntax.mkNullNode #[])
          sAfterTy.bindState fun s =>
            if s.hasError then s else
            (symbolFn ")" ctx s).bindState fun s =>
              if s.hasError then s else
              let bPref := s.stxStack.getD (iniSz + 1)
              let ids   := s.stxStack.getD (iniSz + 2)
              let vPref := if Nat.beq s.stackSize (iniSz + 7) then s.stxStack.getD (iniSz + 4) else s.stxStack.getD (iniSz + 3)
              let ty    := if Nat.beq s.stackSize (iniSz + 7) then s.stxStack.getD (iniSz + 5) else s.stxStack.getD (iniSz + 4)
              let s := s.shrinkStack iniSz
              s.pushSyntax (Syntax.mkNode SyntaxKind.explicitBinder #[bPref, ids, vPref, ty])

/-- Parse an implicit binder `{0 α β : Type}` or `{α β}`. -/
def implicitBinderFn (termRec : ParserFn) : ParserFn := fun ctx s =>
  s.bindState fun s =>
    let iniSz := s.stackSize
    (symbolFn "{" ctx s).bindState fun s =>
      if s.hasError then s else
      (binderPrefixFn ctx s).bindState fun s =>
      (binderIdentsFn ctx s).bindState fun s =>
        if s.hasError then s else
        bindPeek ctx s fun tok? s =>
          let sAfterTy := match tok? with
            | some (.atom _ ":") =>
              (symbolFn ":" ctx s).bindState fun s =>
              (valuePrefixFn ctx s).bindState fun s =>
                withPrecFn 0 termRec ctx s
            | _ =>
              let s := s.pushSyntax (Syntax.mkNode SyntaxKind.valuePrefix #[])
              s.pushSyntax (Syntax.mkNullNode #[])
          sAfterTy.bindState fun s =>
            if s.hasError then s else
            (symbolFn "}" ctx s).bindState fun s =>
              if s.hasError then s else
              let bPref := s.stxStack.getD (iniSz + 1)
              let ids   := s.stxStack.getD (iniSz + 2)
              let vPref := if Nat.beq s.stackSize (iniSz + 7) then s.stxStack.getD (iniSz + 4) else s.stxStack.getD (iniSz + 3)
              let ty    := if Nat.beq s.stackSize (iniSz + 7) then s.stxStack.getD (iniSz + 5) else s.stxStack.getD (iniSz + 4)
              let s := s.shrinkStack iniSz
              s.pushSyntax (Syntax.mkNode SyntaxKind.implicitBinder #[bPref, ids, vPref, ty])

/-- Parse a strict-implicit binder `⦃x : A⦄` or `{{x : A}}`. -/
def strictImplicitBinderFn (termRec : ParserFn) : ParserFn := fun ctx s =>
  s.bindState fun s =>
    let iniSz := s.stackSize
    bindPeek ctx s fun tok? s =>
      let closeSym := match tok? with
        | some (.atom _ "{{") => "}}"
        | _ => "⦄"
      let openSym := if closeSym == "}}" then "{{" else "⦃"
      (symbolFn openSym ctx s).bindState fun s =>
        if s.hasError then s else
        (binderPrefixFn ctx s).bindState fun s =>
        (binderIdentsFn ctx s).bindState fun s =>
          if s.hasError then s else
          bindPeek ctx s fun tok? s =>
            let sAfterTy := match tok? with
              | some (.atom _ ":") =>
                (symbolFn ":" ctx s).bindState fun s =>
                (valuePrefixFn ctx s).bindState fun s =>
                  withPrecFn 0 termRec ctx s
              | _ =>
                let s := s.pushSyntax (Syntax.mkNode SyntaxKind.valuePrefix #[])
                s.pushSyntax (Syntax.mkNullNode #[])
            sAfterTy.bindState fun s =>
              if s.hasError then s else
              (symbolFn closeSym ctx s).bindState fun s =>
                if s.hasError then s else
                let bPref := s.stxStack.getD (iniSz + 1)
                let ids   := s.stxStack.getD (iniSz + 2)
                let vPref := if Nat.beq s.stackSize (iniSz + 7) then s.stxStack.getD (iniSz + 4) else s.stxStack.getD (iniSz + 3)
                let ty    := if Nat.beq s.stackSize (iniSz + 7) then s.stxStack.getD (iniSz + 5) else s.stxStack.getD (iniSz + 4)
                let s := s.shrinkStack iniSz
                s.pushSyntax (Syntax.mkNode SyntaxKind.strictImplicitBinder #[bPref, ids, vPref, ty])

/-- Parse an instance-implicit binder `[inst : Add α]` or `[Add α]`. -/
def instBinderFn (termRec : ParserFn) : ParserFn := fun ctx s =>
  s.bindState fun s =>
    let iniSz := s.stackSize
    (symbolFn "[" ctx s).bindState fun s =>
      if s.hasError then s else
      let namedAttempt : ParserFn := fun c st =>
        (binderPrefixFn c st).bindState fun st =>
        (binderIdentFn c st).bindState fun st =>
          if st.hasError then st else
          (symbolFn ":" c st).bindState fun st =>
            if st.hasError then st else
            (valuePrefixFn c st).bindState fun st =>
              withPrecFn 0 termRec c st
      let anonAttempt : ParserFn := fun c st =>
        let st := st.pushSyntax (Syntax.mkNode SyntaxKind.binderPrefix #[])
        let st := st.pushSyntax (Syntax.mkSimpleIdent Name.mkAnon)
        let st := st.pushSyntax (Syntax.mkNode SyntaxKind.valuePrefix #[])
        withPrecFn 0 termRec c st
      (tryOrElseFn namedAttempt anonAttempt ctx s).bindState fun s =>
        if s.hasError then s else
        (symbolFn "]" ctx s).bindState fun s =>
          if s.hasError then s else
          let bPref := s.stxStack.getD (iniSz + 1)
          let idStx := s.stxStack.getD (iniSz + 2)
          let (vPref, ty) :=
            if Nat.beq s.stackSize (iniSz + 7) then
              (s.stxStack.getD (iniSz + 4), s.stxStack.getD (iniSz + 5))
            else
              (s.stxStack.getD (iniSz + 3), s.stxStack.getD (iniSz + 4))
          let s := s.shrinkStack iniSz
          s.pushSyntax (Syntax.mkNode SyntaxKind.instBinder #[bPref, Syntax.mkNullNode #[idStx], vPref, ty])

/-- Parse any bracketed binder `(...)`, `{...}`, `⦃...⦄`, `[...]`. -/
def bracketedBinderFn (termRec : ParserFn) : ParserFn := fun ctx s =>
  bindPeek ctx s fun tok? s =>
    match tok? with
    | some (.atom _ "(") => explicitBinderFn termRec ctx s
    | some (.atom _ "{") => implicitBinderFn termRec ctx s
    | some (.atom _ "⦃") | some (.atom _ "{{") => strictImplicitBinderFn termRec ctx s
    | some (.atom _ "[") => instBinderFn termRec ctx s
    | _ => s.mkUnexpectedError "expected binder"

/-- Parse a `fun` / `forall` binder: either a bracketed binder or an unparenthesized identifier `x`. -/
def simpleOrBracketedBinderFn (termRec : ParserFn) : ParserFn := fun ctx s =>
  bindPeek ctx s fun tok? s =>
    match tok? with
    | some (.atom _ "(") | some (.atom _ "{") | some (.atom _ "⦃")
    | some (.atom _ "{{") | some (.atom _ "[") =>
      bracketedBinderFn termRec ctx s
    | _ =>
      let iniSz := s.stackSize
      (binderIdentFn ctx s).bindState fun s =>
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
  s.bindState fun s =>
    let term0 := withPrecFn 0 termRec
    let iniSz := s.stackSize
    (symbolFn "|" ctx s).bindState fun s =>
      if s.hasError then s else
      (sepBy1Fn term0 (symbolFn ",") false ctx s).bindState fun s =>
        if s.hasError then s else
        (orelseFn (symbolFn "=>") (symbolFn "↦") ctx s).bindState fun s =>
          if s.hasError then s else
          (term0 ctx s).bindState fun s =>
            s.mkNode SyntaxKind.matchAlt iniSz

/-- Parse a leading expression (atoms, binders, `fun`, `forall`, `let`, `let borrow`, `if`, `match`, `by`). -/
def leadTermFn (termRec : ParserFn) (tacticFuel : Nat) : ParserFn := fun ctx s =>
  let term0 := withPrecFn 0 termRec
  bindPeek ctx s fun tok? s =>
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
      (identFn ctx s).bindState fun s =>
        bindPeek ctx s fun nextTok? s =>
          match nextTok? with
          | some (.atom _ ".{") =>
            (optUnivArgsFn ctx s).bindState fun s =>
              s.mkNode SyntaxKind.explicitTerm iniSz
          | _ => s
    -- 3. Keywords and leading symbols
    | some (.atom _ sym) =>
      match sym with
      | "_" =>
        let iniSz := s.stackSize
        (symbolFn "_" ctx s).bindState fun s =>
          s.mkNode SyntaxKind.holeTerm iniSz
      | "sorry" =>
        let iniSz := s.stackSize
        (symbolFn "sorry" ctx s).bindState fun s =>
          s.mkNode SyntaxKind.sorryTerm iniSz
      | "Prop" =>
        let iniSz := s.stackSize
        (symbolFn "Prop" ctx s).bindState fun s =>
          s.mkNode SyntaxKind.propTerm iniSz
      | "Type" =>
        let iniSz := s.stackSize
        (symbolFn "Type" ctx s).bindState fun s =>
          bindPeek ctx s fun nextTok? s =>
            let sAfterLvl := match nextTok? with
              | some (.node _ k _) =>
                if k == SyntaxKind.numLit then levelFn ctx s
                else s.pushSyntax (Syntax.mkNullNode #[])
              | some (.ident ..) | some (.atom _ "(") =>
                optionalFn (withPrecFn maxPrec (levelAtomFn levelFn)) ctx s
              | _ => s.pushSyntax (Syntax.mkNullNode #[])
            sAfterLvl.bindState fun s =>
              s.mkNode SyntaxKind.typeTerm iniSz
      | "Sort" =>
        let iniSz := s.stackSize
        (symbolFn "Sort" ctx s).bindState fun s =>
        (optionalFn (withPrecFn maxPrec (levelAtomFn levelFn)) ctx s).bindState fun s =>
          s.mkNode SyntaxKind.sortTerm iniSz
      | "@" =>
        let iniSz := s.stackSize
        (symbolFn "@" ctx s).bindState fun s =>
        (identFn ctx s).bindState fun s =>
        (optUnivArgsFn ctx s).bindState fun s =>
          s.mkNode SyntaxKind.explicitTerm iniSz
      | "fun" | "λ" =>
        let iniSz := s.stackSize
        (tokenFn ctx s).bindState fun s =>
        (many1Fn (simpleOrBracketedBinderFn termRec) ctx s).bindState fun s =>
        (orelseFn (symbolFn "=>") (symbolFn "↦") ctx s).bindState fun s =>
        (term0 ctx s).bindState fun s =>
          s.mkNode SyntaxKind.funTerm iniSz
      | "forall" | "∀" =>
        let iniSz := s.stackSize
        (tokenFn ctx s).bindState fun s =>
        (many1Fn (simpleOrBracketedBinderFn termRec) ctx s).bindState fun s =>
          if s.hasError then s else
          bindPeek ctx s fun sepTok? s =>
            match sepTok? with
            | some (.atom _ ":") =>
              -- Could be either unparenthesized typed binders `∀ a b c : T, body` OR `forall (x : A) : body`
              (symbolFn ":" ctx s).bindState fun s =>
              (valuePrefixFn ctx s).bindState fun s =>
              (term0 ctx s).bindState fun s =>
                if s.hasError then s else
                bindPeek ctx s fun afterTyTok? s =>
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
                    (symbolFn "," ctx s).bindState fun s =>
                    (valuePrefixFn ctx s).bindState fun s =>
                    (term0 ctx s).bindState fun s =>
                      s.mkNode SyntaxKind.forallTerm iniSz
                  | _ =>
                    s.mkNode SyntaxKind.forallTerm iniSz
            | _ =>
              (symbolFn "," ctx s).bindState fun s =>
              (valuePrefixFn ctx s).bindState fun s =>
              (term0 ctx s).bindState fun s =>
                s.mkNode SyntaxKind.forallTerm iniSz
      | "let" =>
        let iniSz := s.stackSize
        (symbolFn "let" ctx s).bindState fun s =>
          bindPeek ctx s fun afterLet? s =>
            let isBorrow := match afterLet? with
              | some (.ident _ _ (.str (.anonymous _) "borrow" _) _) => true
              | _ => false
            let sBorrow := if isBorrow then nonReservedSymbolFn "borrow" ctx s else s
            sBorrow.bindState fun s =>
            (binderPrefixFn ctx s).bindState fun s =>
            (binderIdentFn ctx s).bindState fun s =>
              if s.hasError then s else
              (manyFn (simpleOrBracketedBinderFn termRec) ctx s).bindState fun s =>
              (optionalFn (fun c st =>
                (symbolFn ":" c st).bindState fun st =>
                  if st.hasError then st else
                  (valuePrefixFn c st).bindState fun st =>
                    term0 c st) ctx s).bindState fun s =>
                if s.hasError then s else
                (symbolFn ":=" ctx s).bindState fun s =>
                  if s.hasError then s else
                  (term0 ctx s).bindState fun s =>
                    if s.hasError then s else
                    (optionalFn (orelseFn (symbolFn ";") (symbolFn "in")) ctx s).bindState fun s =>
                    (term0 ctx s).bindState fun s =>
                      s.mkNode (if isBorrow then SyntaxKind.letBorrowTerm else SyntaxKind.letTerm) iniSz
      | "have" =>
        let iniSz := s.stackSize
        (symbolFn "have" ctx s).bindState fun s =>
        (binderIdentFn ctx s).bindState fun s =>
          if s.hasError then s else
          (optionalFn (seqFn (symbolFn ":") term0) ctx s).bindState fun s =>
            if s.hasError then s else
            (symbolFn ":=" ctx s).bindState fun s =>
              if s.hasError then s else
              (term0 ctx s).bindState fun s =>
                if s.hasError then s else
                (optionalFn (orelseFn (symbolFn ";") (symbolFn "in")) ctx s).bindState fun s =>
                (term0 ctx s).bindState fun s =>
                  s.mkNode SyntaxKind.haveTerm iniSz
      | "if" =>
        let iniSz := s.stackSize
        (symbolFn "if" ctx s).bindState fun s =>
          let depCondAttempt : ParserFn := fun c st =>
            (identFn c st).bindState fun st =>
            (symbolFn ":" c st).bindState fun st =>
              term0 c st
          let plainCondAttempt : ParserFn := fun c st =>
            let st := st.pushSyntax (Syntax.mkNullNode #[])
            term0 c st
          (tryOrElseFn depCondAttempt plainCondAttempt ctx s).bindState fun s =>
          (symbolFn "then" ctx s).bindState fun s =>
          (term0 ctx s).bindState fun s =>
          (symbolFn "else" ctx s).bindState fun s =>
          (term0 ctx s).bindState fun s =>
            s.mkNode SyntaxKind.ifTerm iniSz
      | "match" =>
        let iniSz := s.stackSize
        (symbolFn "match" ctx s).bindState fun s =>
        (sepBy1Fn term0 (symbolFn ",") false ctx s).bindState fun s =>
        (symbolFn "with" ctx s).bindState fun s =>
        (many1Fn (matchAltFn termRec) ctx s).bindState fun s =>
          s.mkNode SyntaxKind.matchTerm iniSz
      | "by" =>
        let iniSz := s.stackSize
        (symbolFn "by" ctx s).bindState fun s =>
        (tacticSeqStep termRec tacticFuel ctx s).bindState fun s =>
          s.mkNode SyntaxKind.byTactic iniSz
      | "(" =>
        let depPiAttempt : ParserFn := fun c st =>
          let pSz := st.stackSize
          (many1Fn (bracketedBinderFn termRec) c st).bindState fun st =>
            if st.hasError then st else
            (orelseFn (symbolFn "→") (symbolFn "->") c st).bindState fun st =>
              if st.hasError then st else
              (valuePrefixFn c st).bindState fun st =>
              (withPrecFn (arrowPrec - 1) termRec c st).bindState fun st =>
                st.mkNode SyntaxKind.forallTerm pSz
        let parenAttempt : ParserFn := fun c st =>
          let pSz := st.stackSize
          (symbolFn "(" c st).bindState fun st =>
            if st.hasError then st else
            bindPeek c st fun next? st =>
              match next? with
              | some (.atom _ ")") =>
                (symbolFn ")" c st).bindState fun st =>
                  st.mkNode SyntaxKind.tupleTerm pSz
              | _ =>
                (term0 c st).bindState fun st =>
                  if st.hasError then st else
                  bindPeek c st fun afterFirst? st =>
                    match afterFirst? with
                    | some (.atom _ ":") =>
                      (symbolFn ":" c st).bindState fun st =>
                      (valuePrefixFn c st).bindState fun st =>
                      (term0 c st).bindState fun st =>
                      (symbolFn ")" c st).bindState fun st =>
                        st.mkNode SyntaxKind.typeAscription pSz
                    | some (.atom _ ",") =>
                      (symbolFn "," c st).bindState fun st =>
                      (sepBy1Fn term0 (symbolFn ",") true c st).bindState fun st =>
                      (symbolFn ")" c st).bindState fun st =>
                        st.mkNode SyntaxKind.tupleTerm pSz
                    | _ =>
                      let inner := st.stxStack.back
                      (symbolFn ")" c st).bindState fun st =>
                        if st.hasError then st else
                        let st := st.shrinkStack pSz
                        st.pushSyntax inner
        tryOrElseFn depPiAttempt parenAttempt ctx s
      | "{" | "⦃" | "{{" =>
        let depPiAttempt : ParserFn := fun c st =>
          let pSz := st.stackSize
          (many1Fn (bracketedBinderFn termRec) c st).bindState fun st =>
            if st.hasError then st else
            (orelseFn (symbolFn "→") (symbolFn "->") c st).bindState fun st =>
              if st.hasError then st else
              (valuePrefixFn c st).bindState fun st =>
              (withPrecFn (arrowPrec - 1) termRec c st).bindState fun st =>
                st.mkNode SyntaxKind.forallTerm pSz
        let structInstAttempt : ParserFn := fun c st =>
          let pSz := st.stackSize
          (symbolFn "{" c st).bindState fun st =>
            if st.hasError then st else
            let withAttempt : ParserFn := fun c2 st2 =>
              (term0 c2 st2).bindState fun st2 =>
                if st2.hasError then st2 else
                nonReservedSymbolFn "with" c2 st2
            let noWith : ParserFn := fun _ st2 =>
              st2.pushSyntax (Syntax.mkNullNode #[])
            (tryOrElseFn withAttempt noWith c st).bindState fun st =>
              let fieldAssign : ParserFn := fun c2 st2 =>
                let fSz := st2.stackSize
                (identFn c2 st2).bindState fun st2 =>
                (symbolFn ":=" c2 st2).bindState fun st2 =>
                (term0 c2 st2).bindState fun st2 =>
                  st2.mkNode SyntaxKind.structFieldAssign fSz
              (sepByFn fieldAssign (symbolFn ",") true c st).bindState fun st =>
              (symbolFn "}" c st).bindState fun st =>
                st.mkNode SyntaxKind.structInst pSz
        tryOrElseFn depPiAttempt structInstAttempt ctx s
      | "[" =>
        let depPiAttempt : ParserFn := fun c st =>
          let pSz := st.stackSize
          (many1Fn (bracketedBinderFn termRec) c st).bindState fun st =>
            if st.hasError then st else
            (orelseFn (symbolFn "→") (symbolFn "->") c st).bindState fun st =>
              if st.hasError then st else
              (valuePrefixFn c st).bindState fun st =>
              (withPrecFn (arrowPrec - 1) termRec c st).bindState fun st =>
                st.mkNode SyntaxKind.forallTerm pSz
        let listLitAttempt : ParserFn := fun c st =>
          let pSz := st.stackSize
          (symbolFn "[" c st).bindState fun st =>
            if st.hasError then st else
            (sepByFn term0 (symbolFn ",") true c st).bindState fun st =>
            (symbolFn "]" c st).bindState fun st =>
              st.mkNode SyntaxKind.listLit pSz
        tryOrElseFn depPiAttempt listLitAttempt ctx s
      | "⟨" =>
        let iniSz := s.stackSize
        (symbolFn "⟨" ctx s).bindState fun s =>
        (sepByFn term0 (symbolFn ",") true ctx s).bindState fun s =>
        (symbolFn "⟩" ctx s).bindState fun s =>
          s.mkNode SyntaxKind.anonCtor iniSz
      | "-" | "!" | "¬" =>
        let iniSz := s.stackSize
        (tokenFn ctx s).bindState fun s =>
        (withPrecFn leadPrec termRec ctx s).bindState fun s =>
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
    s.bindState fun s =>
      if s.hasError then s else
      bindPeek ctx s fun tok? s =>
        match tok? with
        | none => s
        | some tok =>
          -- 1. Field or index projection `.field` / `.0` (tightest binding, `maxPrec`)
          if Syntax.getAtomVal tok == "." && Nat.ble (ctx.prec + 1) maxPrec then
            let iniSz := s.stackSize
            (symbolFn "." ctx s).bindState fun s =>
            (orelseFn identFn numLitFn ctx s).bindState fun s =>
              if s.hasError then s else
              (s.mkTrailingNode SyntaxKind.projTerm iniSz maxPrec).bindState fun s =>
                trailingTermLoop termRec ctx s fuel
          -- 2. Non-dependent function arrow `A → !B` / `A -> ~B` (precedence `arrowPrec := 25`, right-assoc)
          else if (Syntax.getAtomVal tok == "→" || Syntax.getAtomVal tok == "->") && Nat.ble ctx.prec arrowPrec then
            let iniSz := s.stackSize
            (tokenFn ctx s).bindState fun s =>
            (valuePrefixFn ctx s).bindState fun s =>
            (withPrecFn arrowPrec termRec ctx s).bindState fun s =>
              if s.hasError then s else
              (s.mkTrailingNode SyntaxKind.arrowTerm iniSz arrowPrec).bindState fun s =>
                trailingTermLoop termRec ctx s fuel
          -- 3. Registered binary infix operator
          else
            match findInfixOp? ctx.env (Syntax.getAtomVal tok) ctx.prec with
            | some op =>
              let iniSz := s.stackSize
              (tokenFn ctx s).bindState fun s =>
                let rhsMinPrec := match op.fixity with
                  | .infixl => op.prec + 1
                  | .infixr => op.prec
                  | _       => op.prec + 1
                (withPrecFn rhsMinPrec termRec ctx s).bindState fun s =>
                  if s.hasError then s else
                  (s.mkTrailingNode op.kind iniSz op.prec).bindState fun s =>
                    trailingTermLoop termRec ctx s fuel
            | none =>
              -- 4. Juxtaposition application `f arg` when `ctx.prec < argPrec` (on the same line)
              if Nat.ble (ctx.prec + 1) argPrec && !hasLeadingNewline tok && canStartArg ctx.env tok then
                let iniSz := s.stackSize
                (withPrecFn argPrec termRec ctx s).bindState fun s =>
                  if s.hasError then s else
                  (s.mkTrailingNode SyntaxKind.appTerm iniSz argPrec).bindState fun s =>
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
