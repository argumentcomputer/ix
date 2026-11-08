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
   "→", "->", "←", "<-", "↔", "<->", "↦", "=>", "<;>", "·", "∀", "∃", "λ",
   "+", "-", "*", "/", "%", "^", "++",
   "==", "!=", "≠", "<=", "≤", "<", ">=", "≥", ">", "=",
   "&&", "||", "∧", "/\\", "∨", "\\/", "¬",
   "|>", "<|", "$", "`(", "`",
   "!", "~", "&", ".{"]

/-- Reserved keywords that cannot be parsed as plain identifiers unless escaped with `«...»`. -/
def defaultKeywords : List String :=
  ["def", "abbrev", "theorem", "lemma", "axiom", "opaque", "instance",
   "inductive", "structure", "class", "where", "extending", "extends", "deriving",
   "mutual", "end", "namespace", "section", "open", "export", "variable", "universe",
   "import", "private", "protected", "noncomputable", "partial", "unsafe",
   "fun", "forall", "let", "have", "in", "if", "then", "else", "match", "with",
   "by", "calc", "Prop", "Type", "Sort", "sorry", "_"]

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
    { tokens := .node tv tch, keywords := .node kv kch, operators := defaultOperators, notations := [] }

/-- Register a new token in `IxParserEnv`. -/
def IxParserEnv.addToken (env : IxParserEnv) (sym : String) : IxParserEnv :=
  match env with
  | ⟨tokens, keywords, operators, notations⟩ =>
    match tokens.insert sym sym with
    | .node tv tch => ⟨.node tv tch, keywords, operators, notations⟩

def IxParserEnv.addOperator (env : IxParserEnv) (op : OperatorSpec) : IxParserEnv :=
  match env.addToken op.symbol with
  | ⟨tokens, keywords, operators, notations⟩ => ⟨tokens, keywords, op :: operators, notations⟩

/-- Single-character delimiter brackets/separators that always form their own token. -/
def isSingleDelimChar (c : Char) : Bool :=
  c == '(' || c == ')' || c == '[' || c == ']' ||
  c == '{' || c == '}' || c == ',' || c == ';'

/-- Scan a run of operator/symbol characters (non-space, non-ident, non-single-delimiter). -/
def scanSymRunChars : List Char → List Char → List Char × List Char
  | [], revAcc => ([], revAcc.reverse)
  | c :: cs, revAcc =>
    if isSpaceChar c || isIdFirst c || isDigitChar c || isSingleDelimChar c then
      (c :: cs, revAcc.reverse)
    else
      scanSymRunChars cs (c :: revAcc)

/-- Split a notation string literal (e.g. `"my_add("` -> `["my_add", "("]`) into atomic lexer tokens. -/
def splitNotationLiteralAux : Nat → List Char → List String → List String
  | 0, _, revToks => revToks.reverse
  | _, [], revToks => revToks.reverse
  | fuel + 1, c :: cs, revToks =>
    if isSpaceChar c then
      splitNotationLiteralAux fuel cs revToks
    else if isSingleDelimChar c then
      splitNotationLiteralAux fuel cs (String.singleton c :: revToks)
    else if isIdFirst c then
      let (rem, partCs, _) := scanIdentRestChars cs 0 [c]
      splitNotationLiteralAux fuel rem (String.ofList partCs :: revToks)
    else
      let (rem, symCs) := scanSymRunChars cs [c]
      splitNotationLiteralAux fuel rem (String.ofList symCs :: revToks)

def splitNotationLiteral (s : String) : List String :=
  let cs := s.toList
  splitNotationLiteralAux (cs.length + 1) cs []

/-- Register a `NotationRule` and all of its non-identifier symbol tokens in `IxParserEnv`. -/
def IxParserEnv.addNotation (env : IxParserEnv) (rule : NotationRule) : IxParserEnv :=
  let envWithToks := rule.items.foldl (fun acc item =>
    match item with
    | .sym s =>
      match s.toList with
      | c :: _ => if isIdFirst c then acc else acc.addToken s
      | []     => acc
    | .var .. => acc) env
  match envWithToks with
  | ⟨tokens, keywords, operators, notations⟩ =>
    ⟨tokens, keywords, operators, rule :: notations⟩

/-- Merge custom operators and notations from `imported` into `base`. -/
def IxParserEnv.merge (base imported : IxParserEnv) : IxParserEnv :=
  let env1 := imported.operators.foldr (fun op acc =>
    if acc.operators.any (fun o => o.symbol == op.symbol && o.fixity == op.fixity) then acc
    else acc.addOperator op) base
  imported.notations.foldr (fun rule acc =>
    if acc.notations.any (fun r => r.ruleName == rule.ruleName) then acc
    else acc.addNotation rule) env1

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
    Nat.ble minPrec op.prec && op.symbol == sym &&
    (op.fixity == .infixl || op.fixity == .infixr || op.fixity == .infixn)

/-- Look up a prefix operator spec matching `sym`. -/
def findPrefixOp? (env : IxParserEnv) (sym : String) : Option OperatorSpec :=
  env.operators.find? fun op =>
    op.fixity == .prefixOp && op.symbol == sym

/-- Look up a postfix operator spec matching `sym` at or above `minPrec`. -/
def findPostfixOp? (env : IxParserEnv) (sym : String) (minPrec : Nat) : Option OperatorSpec :=
  env.operators.find? fun op =>
    op.fixity == .postfixOp && Nat.ble minPrec op.prec && op.symbol == sym

/-- True if `sym` appears only as a non-leading delimiter in `env.notations` (so it cannot start an argument). -/
def isNonLeadingNotationSym (env : IxParserEnv) (sym : String) : Bool :=
  match env.notations with
  | [] => false
  | nots =>
    (nots.any fun r =>
      match r.items with
      | _ :: tail => tail.any fun it => match it with | .sym s => s == sym | _ => false
      | [] => false) &&
    !(nots.any fun r =>
      match r.items with
      | .sym s :: _ => s == sym
      | _ => false)

/-- True if `sym` is a relational operator allowed in a bounded quantifier binder (`∀ x > 0, ...`). -/
def isBinderRelOp (sym : String) : Bool :=
  sym == ">" || sym == "<" || sym == "≥" || sym == ">=" ||
  sym == "≤" || sym == "<=" || sym == "≠" || sym == "!="

/-- Check if a token can start a function argument in juxtaposition `f a`. -/
def canStartArg (env : IxParserEnv) : Ix.Syntax → Bool
  | .ident _ _ (.str (.anonymous _) "from" _) _ => false
  | .ident .. => !isNonLeadingNotationSym env ""
  | .node _ k _ =>
    k == SyntaxKind.numLit || k == SyntaxKind.strLit ||
    k == SyntaxKind.charLit || k == SyntaxKind.hashRef
  | .atom _ sym =>
    sym == "(" || sym == "⟨" || sym == "[" || sym == "{" ||
    sym == "@" || sym == "_" || sym == "Prop" || sym == "Type" ||
    sym == "Sort" || sym == "true" || sym == "false" || sym == "sorry" ||
    sym == "$" || sym == "`(" || sym == "`" ||
    !(isKeyword env sym || isNonLeadingNotationSym env sym ||
      sym == ")" || sym == "}" || sym == "]" || sym == "⦄" ||
      sym == "}}" || sym == "⟩" || sym == ":" || sym == ":=" || sym == ";" ||
      sym == "," || sym == "|" || sym == "=>" || sym == "↦" || sym == "→" ||
      sym == "->" || sym == "in" || sym == "then" || sym == "else" || sym == "with" ||
      sym == "from" || sym == "where" || sym == "end" ||
      (env.operators.any fun op => op.symbol == sym && op.fixity != .prefixOp))
  | .missing => false

/-- Parse an explicit binder `(0 x y : !A)` or `(x : A)` or bounded `(x > 0)` or `(x)`. -/
def explicitBinderFn (termRec : ParserFn) : ParserFn := fun ctx s =>
  s.bindState fun s =>
    let iniSz := s.stackSize
    (symbolFn "(" ctx s).bindState fun s =>
      if s.hasError then s else
      let s := s.popSyntax
      (binderPrefixFn ctx s).bindState fun s =>
      (binderIdentsFn ctx s).bindState fun s =>
        if s.hasError then s else
        bindPeek ctx s fun tok? s =>
          let sAfterTy := match tok? with
            | some (.atom _ ":") =>
              (symbolFn ":" ctx s).bindState fun s =>
                let s := s.popSyntax
                (valuePrefixFn ctx s).bindState fun s =>
                  withPrecFn 0 termRec ctx s
            | some (.atom _ sym) =>
              if isBinderRelOp sym then
                (tokenFn ctx s).bindState fun s =>
                  let opTok := s.stxStack.back
                  let s := s.popSyntax
                  (withPrecFn 0 termRec ctx s).bindState fun s =>
                    if s.hasError then s else
                    let rhsStx := s.stxStack.back
                    let s := s.popSyntax
                    let s := s.pushSyntax (Syntax.mkNode SyntaxKind.valuePrefix #[])
                    s.pushSyntax (Syntax.mkNode SyntaxKind.binOpTerm #[Syntax.mkSimpleAtom "_bound", opTok, rhsStx])
              else
                let s := s.pushSyntax (Syntax.mkNode SyntaxKind.valuePrefix #[])
                s.pushSyntax (Syntax.mkNullNode #[])
            | _ =>
              let s := s.pushSyntax (Syntax.mkNode SyntaxKind.valuePrefix #[])
              s.pushSyntax (Syntax.mkNullNode #[])
          sAfterTy.bindState fun s =>
            if s.hasError then s else
            (symbolFn ")" ctx s).bindState fun s =>
              if s.hasError then s else
              (s.popSyntax).mkNode SyntaxKind.explicitBinder iniSz

/-- Parse an implicit binder `{0 α β : Type}` or `{α β}`. -/
def implicitBinderFn (termRec : ParserFn) : ParserFn := fun ctx s =>
  s.bindState fun s =>
    let iniSz := s.stackSize
    (symbolFn "{" ctx s).bindState fun s =>
      if s.hasError then s else
      let s := s.popSyntax
      (binderPrefixFn ctx s).bindState fun s =>
      (binderIdentsFn ctx s).bindState fun s =>
        if s.hasError then s else
        bindPeek ctx s fun tok? s =>
          let sAfterTy := match tok? with
            | some (.atom _ ":") =>
              (symbolFn ":" ctx s).bindState fun s =>
                let s := s.popSyntax
                (valuePrefixFn ctx s).bindState fun s =>
                  withPrecFn 0 termRec ctx s
            | _ =>
              let s := s.pushSyntax (Syntax.mkNode SyntaxKind.valuePrefix #[])
              s.pushSyntax (Syntax.mkNullNode #[])
          sAfterTy.bindState fun s =>
            if s.hasError then s else
            (symbolFn "}" ctx s).bindState fun s =>
              if s.hasError then s else
              (s.popSyntax).mkNode SyntaxKind.implicitBinder iniSz

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
        let s := s.popSyntax
        (binderPrefixFn ctx s).bindState fun s =>
        (binderIdentsFn ctx s).bindState fun s =>
          if s.hasError then s else
          bindPeek ctx s fun tok? s =>
            let sAfterTy := match tok? with
              | some (.atom _ ":") =>
                (symbolFn ":" ctx s).bindState fun s =>
                  let s := s.popSyntax
                  (valuePrefixFn ctx s).bindState fun s =>
                    withPrecFn 0 termRec ctx s
              | _ =>
                let s := s.pushSyntax (Syntax.mkNode SyntaxKind.valuePrefix #[])
                s.pushSyntax (Syntax.mkNullNode #[])
            sAfterTy.bindState fun s =>
              if s.hasError then s else
              (symbolFn closeSym ctx s).bindState fun s =>
                if s.hasError then s else
                (s.popSyntax).mkNode SyntaxKind.strictImplicitBinder iniSz

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

/-- True if `tok?` starts a sibling `·` / `case` focus block (used to end a focused tactic sequence). -/
def isFocusOrCaseToken : Option Ix.Syntax → Bool
  | some (.atom _ "·") | some (.atom _ ".") => true
  | some (.ident _ _ (.str (.anonymous _) "case" _) _) | some (.atom _ "case") => true
  | _ => false

/-- Parse a recursive `rcases` / `obtain` / `rintro` pattern (`rcasesPat`),
    structurally recursive on `patFuel : Nat`.
    Supports:
    - `_` (`SyntaxKind.rcasesPatWildcard`)
    - `rfl` (`SyntaxKind.rcasesPatRfl`)
    - `x` (`SyntaxKind.rcasesPatIdent`)
    - `⟨p₁, p₂, ...⟩` (`SyntaxKind.rcasesPatTuple`)
    - `(p)` or `(p₁, p₂, ...)`
    - `p₁ | p₂ | ...` (`SyntaxKind.rcasesPatAlt` when `allowAlt = true`) -/
def rcasesPatStep (allowAlt : Bool) : Nat → ParserFn
  | 0 => fun _ s => s.mkUnexpectedError "parser fuel exhausted in rcases pattern"
  | patFuel + 1 => fun ctx s =>
    let patAtom : ParserFn := fun c st =>
      bindPeek c st fun tok? st =>
        let iniSz := st.stackSize
        match tok? with
        | some (.atom _ "_") =>
          (tokenFn c st).bindState fun st =>
            st.mkNode SyntaxKind.rcasesPatWildcard iniSz
        | some (.ident _ _ (.str (.anonymous _) "rfl" _) _) | some (.atom _ "rfl") =>
          (tokenFn c st).bindState fun st =>
            st.mkNode SyntaxKind.rcasesPatRfl iniSz
        | some (.atom _ "⟨") =>
          (symbolFn "⟨" c st).bindState fun st =>
            if st.hasError then st else
            let st := st.popSyntax
            (sepByFn (rcasesPatStep true patFuel) (symbolFn ",") true c st).bindState fun st =>
              if st.hasError then st else
              (symbolFn "⟩" c st).bindState fun st =>
                if st.hasError then st else
                (st.popSyntax).mkNode SyntaxKind.rcasesPatTuple iniSz
        | some (.atom _ "(") =>
          (symbolFn "(" c st).bindState fun st =>
            if st.hasError then st else
            let st := st.popSyntax
            (sepBy1Fn (rcasesPatStep true patFuel) (symbolFn ",") true c st).bindState fun st =>
              if st.hasError then st else
              let itemsNode := st.stxStack.back
              (symbolFn ")" c st).bindState fun st =>
                if st.hasError then st else
                let st := st.shrinkStack iniSz
                let items := Syntax.getArgs itemsNode
                if items.size == 1 then
                  st.pushSyntax (items.getD 0 .missing)
                else
                  st.pushSyntax (Syntax.mkNode SyntaxKind.rcasesPatTuple #[itemsNode])
        | some (.ident ..) =>
          (identFn c st).bindState fun st =>
            st.mkNode SyntaxKind.rcasesPatIdent iniSz
        | _ =>
          st.mkUnexpectedError "expected rcases pattern ('_', 'rfl', identifier, '⟨...⟩', or '(...)')"
    if !allowAlt then
      patAtom ctx s
    else
      let iniSz := s.stackSize
      (sepBy1Fn patAtom (symbolFn "|") false ctx s).bindState fun s =>
        if s.hasError then s else
        let altsNode := s.stxStack.back
        let alts := Syntax.getArgs altsNode
        if alts.size == 1 then
          let s := s.shrinkStack iniSz
          s.pushSyntax (alts.getD 0 .missing)
        else
          s.mkNode SyntaxKind.rcasesPatAlt iniSz

/-- Parse a single `calc` step (`lhs op rhs := proof` or `_ op rhs := proof`).
    Produces `SyntaxKind.calcStep #[relTerm, ":=", proofTerm]`, where `relTerm` is
    a `SyntaxKind.binOpTerm #[lhsOrHole, opAtom, rhs]`. -/
def calcStepFn (termRec : ParserFn) (isFirst : Bool) : ParserFn := fun ctx s =>
  let term0 := withPrecFn 0 termRec
  let iniSz := s.stackSize
  bindPeek ctx s fun tok? s =>
    match tok? with
    | none => s.mkUnexpectedError "end of calc block"
    | some tok =>
      let startsWithUnderscore := match tok with
        | .atom _ "_" => true
        | _ => false
      if !isFirst && !hasLeadingNewline tok && !startsWithUnderscore then
        s.mkUnexpectedError "end of calc block"
      else
        let parseRel : ParserFn := fun c st =>
          if startsWithUnderscore then
            let relSz := st.stackSize
            let hSz := st.stackSize
            (symbolFn "_" c st).bindState fun st =>
              let st := st.mkNode SyntaxKind.holeTerm hSz
              bindPeek c st fun opTok? st =>
                match opTok? with
                | some (.atom _ opSym) =>
                  if opSym == ":=" then
                    st.mkUnexpectedError "expected relation operator after '_' in calc step"
                  else
                    (tokenFn c st).bindState fun st =>
                    (withPrecFn 51 termRec c st).bindState fun st =>
                      if st.hasError then st else
                      st.mkNode SyntaxKind.binOpTerm relSz
                | _ =>
                  st.mkUnexpectedError "expected relation operator after '_' in calc step"
          else
            term0 c st
        (parseRel ctx s).bindState fun s =>
          if s.hasError then s else
          (symbolFn ":=" ctx s).bindState fun s =>
            if s.hasError then s else
            (term0 ctx s).bindState fun s =>
              if s.hasError then s else
              s.mkNode SyntaxKind.calcStep iniSz

/-- Parse one or more `calc` steps into a `nullKind` array node. -/
def calcStepsFn (termRec : ParserFn) : ParserFn := fun ctx s =>
  let iniSz := s.stackSize
  (calcStepFn termRec true ctx s).bindState fun s =>
    if s.hasError then s else
    let s := manyLoop (calcStepFn termRec false) ctx s (ctx.inputCtx.size - s.pos + 1)
    s.mkNode SyntaxKind.nullKind iniSz

/-- Extract the surface string of a token (`.atom` or single-component `.ident`) for notation matching. -/
def tokenText : Ix.Syntax → String
  | .atom _ s => s
  | .ident _ _ (.str (.anonymous _) s _) _ => s
  | _ => ""

/-- Match a sequence of `NotationItem`s after the trigger token, accumulating captured variable `Syntax` nodes. -/
def matchNotationItems (termRec : ParserFn) :
    List NotationItem → List Ix.Syntax → IxParserContext → ParserState → Option (List Ix.Syntax × ParserState)
  | [], revArgs, _, s => some (revArgs.reverse, s)
  | .sym expected :: rest, revArgs, ctx, s =>
    bindPeek ctx s fun tok? s =>
      match tok? with
      | some tok =>
        if tokenText tok == expected then
          let s := tokenFn ctx s
          if s.hasError then none
          else
            let s := s.popSyntax
            matchNotationItems termRec rest revArgs ctx s
        else none
      | none => none
  | .var _ varPrec :: rest, revArgs, ctx, s =>
    let iniSz := s.stackSize
    let s' := withPrecFn varPrec termRec ctx s
    if s'.hasError then none
    else
      let argStx := s'.stxStack.back
      let s' := s'.shrinkStack iniSz
      matchNotationItems termRec rest (argStx :: revArgs) ctx s'

/-- Try matching leading `NotationRule`s whose first item is `.sym firstSym` matching `tokText`. -/
def tryLeadNotationRules (termRec : ParserFn) (tokText : String) :
    List NotationRule → IxParserContext → ParserState → Option ParserState
  | [], _, _ => none
  | rule :: rest, ctx, s =>
    match rule.items with
    | .sym firstSym :: remItems =>
      if firstSym == tokText then
        let iniSz := s.stackSize
        let iniPos := s.pos
        let s1 := (tokenFn ctx s).popSyntax
        match matchNotationItems termRec remItems [] ctx s1 with
        | some (capturedArgs, s2) =>
          let nodeArgs := Syntax.mkSimpleIdent rule.ruleName :: capturedArgs
          let callNode := Syntax.mkNode SyntaxKind.macroCall (Array.mk nodeArgs)
          some (s2.pushSyntax callNode)
        | none =>
          tryLeadNotationRules termRec tokText rest ctx (s.restore iniSz iniPos)
      else
        tryLeadNotationRules termRec tokText rest ctx s
    | _ =>
      tryLeadNotationRules termRec tokText rest ctx s

/-- Try matching trailing `NotationRule`s whose items start with `.var _ :: .sym secondSym :: remItems`. -/
def tryTrailNotationRules (termRec : ParserFn) (tokText : String) :
    List NotationRule → IxParserContext → ParserState → Option ParserState
  | [], _, _ => none
  | rule :: rest, ctx, s =>
    match rule.items with
    | .var _ _ :: .sym secondSym :: remItems =>
      if Nat.ble ctx.prec rule.prec && secondSym == tokText then
        let iniSz := s.stackSize
        let iniPos := s.pos
        let lhsStx := s.stxStack.back
        let s1 := (tokenFn ctx s).popSyntax
        match matchNotationItems termRec remItems [lhsStx] ctx s1 with
        | some (capturedArgs, s2) =>
          let s2 := s2.shrinkStack (iniSz - 1)
          let nodeArgs := Syntax.mkSimpleIdent rule.ruleName :: capturedArgs
          let callNode := Syntax.mkNode SyntaxKind.macroCall (Array.mk nodeArgs)
          some (s2.pushSyntax callNode)
        | none =>
          tryTrailNotationRules termRec tokText rest ctx (s.restore iniSz iniPos)
      else
        tryTrailNotationRules termRec tokText rest ctx s
    | _ =>
      tryTrailNotationRules termRec tokText rest ctx s

/-- Parse a tactic sequence or single combinator step, structurally recursive on `fuel : Nat`. -/
def tacticSeqCore (termRec : ParserFn) (stopAtFocus : Bool) (singleStep : Bool) : Nat → ParserFn
  | 0 => fun _ s => s.mkUnexpectedError "parser fuel exhausted in tactic"
  | fuel + 1 =>
    let term0 := withPrecFn 0 termRec
    let termArg := withPrecFn argPrec termRec
    let sameLineBinderIdent : ParserFn := fun c st =>
      let (t?, st) := peekToken c st
      match t? with
      | some tok =>
        if hasLeadingNewline tok then st.mkUnexpectedError "newline after tactic binder"
        else binderIdentFn c st
      | none => st.mkUnexpectedError "end of tactic binder"
    let sameLineIdent : ParserFn := fun c st =>
      let (t?, st) := peekToken c st
      match t? with
      | some tok =>
        if hasLeadingNewline tok then st.mkUnexpectedError "newline after tactic identifier"
        else identFn c st
      | none => st.mkUnexpectedError "end of tactic identifier"
    let sameLineTerm0 : ParserFn := fun c st =>
      let (t?, st) := peekToken c st
      match t? with
      | some tok =>
        if hasLeadingNewline tok then st.mkUnexpectedError "newline before optional tactic term"
        else term0 c st
      | none => st.mkUnexpectedError "end of optional tactic term"
    let sameLineTermArg : ParserFn := fun c st =>
      let (t?, st) := peekToken c st
      match t? with
      | some tok =>
        if hasLeadingNewline tok then st.mkUnexpectedError "newline before tactic argument"
        else termArg c st
      | none => st.mkUnexpectedError "end of tactic argument"
    let sameLineRcasesPatAtom : ParserFn := fun c st =>
      let (t?, st) := peekToken c st
      match t? with
      | some tok =>
        if hasLeadingNewline tok then st.mkUnexpectedError "newline after rintro pattern"
        else rcasesPatStep false 32 c st
      | none => st.mkUnexpectedError "end of rintro pattern"
    let tacticAlt : ParserFn := fun ctx s =>
      let iniSz := s.stackSize
      let s := symbolFn "|" ctx s
      if s.hasError then s else
      let s := identFn ctx s
      let s := manyFn binderIdentFn ctx s
      let s := orelseFn (symbolFn "=>") (symbolFn "↦") ctx s
      let s := tacticSeqCore termRec false false fuel ctx s
      s.mkNode SyntaxKind.tacticAlt iniSz
    let oneTactic : ParserFn := fun ctx s =>
      let (tok?, s) := peekToken ctx s
      let iniSz := s.stackSize
      match tok? with
      | some (.atom _ "(") =>
        let s := tokenFn ctx s
        let s := tacticSeqCore termRec false false fuel ctx s
        let s := symbolFn ")" ctx s
        s.mkNode SyntaxKind.tacticParen iniSz
      | some (.atom _ "·") | some (.atom _ ".") =>
        let s := tokenFn ctx s
        let s := tacticSeqCore termRec true false fuel ctx s
        s.mkNode SyntaxKind.tacticFocus iniSz
      | some (.ident _ _ (.str (.anonymous _) kw _) _) | some (.atom _ kw) =>
        match kw with
        | "case" =>
          let s := tokenFn ctx s
          let s := identFn ctx s
          let s := manyFn sameLineBinderIdent ctx s
          let s := orelseFn (symbolFn "=>") (symbolFn "↦") ctx s
          let s := tacticSeqCore termRec true false fuel ctx s
          s.mkNode SyntaxKind.tacticCase iniSz
        | "first" =>
          let s := tokenFn ctx s
          let firstBranch : ParserFn := fun c st =>
            let st := symbolFn "|" c st
            if st.hasError then st else
            let st := st.popSyntax
            tacticSeqCore termRec false false fuel c st
          let s := many1Fn firstBranch ctx s
          s.mkNode SyntaxKind.tacticFirst iniSz
        | "try" =>
          let s := tokenFn ctx s
          let s := tacticSeqCore termRec stopAtFocus true fuel ctx s
          s.mkNode SyntaxKind.tacticTry iniSz
        | "repeat" =>
          let s := tokenFn ctx s
          let s := tacticSeqCore termRec stopAtFocus true fuel ctx s
          s.mkNode SyntaxKind.tacticRepeat iniSz
        | "all_goals" =>
          let s := tokenFn ctx s
          let s := tacticSeqCore termRec stopAtFocus true fuel ctx s
          s.mkNode SyntaxKind.tacticAllGoals iniSz
        | "any_goals" =>
          let s := tokenFn ctx s
          let s := tacticSeqCore termRec stopAtFocus true fuel ctx s
          s.mkNode SyntaxKind.tacticAnyGoals iniSz
        | "intro" | "intros" =>
          let s := tokenFn ctx s
          let s := manyFn sameLineBinderIdent ctx s
          s.mkNode SyntaxKind.tacticIntro iniSz
        | "rintro" | "rintros" =>
          let s := tokenFn ctx s
          let s := manyFn sameLineRcasesPatAtom ctx s
          let s := optionalFn (seqFn (symbolFn ":") term0) ctx s
          s.mkNode SyntaxKind.tacticRintro iniSz
        | "rcases" =>
          let s := tokenFn ctx s
          let namedTarget : ParserFn := fun c st =>
            (identFn c st).bindState fun st =>
              if st.hasError then st else
              (symbolFn ":" c st).bindState fun st =>
                if st.hasError then st else
                let st := st.popSyntax
                term0 c st
          let unnamedTarget : ParserFn := fun c st =>
            let st := st.pushSyntax (Syntax.mkSimpleIdent Name.mkAnon)
            term0 c st
          let s := tryOrElseFn namedTarget unnamedTarget ctx s
          let s := optionalFn (seqFn (symbolFn "with") (rcasesPatStep true 32)) ctx s
          s.mkNode SyntaxKind.tacticRcases iniSz
        | "obtain" =>
          let s := tokenFn ctx s
          let (tNext?, s) := peekToken ctx s
          let s := match tNext? with
            | some (.atom _ ":") | some (.atom _ ":=") =>
              s.pushSyntax (Syntax.mkNode SyntaxKind.rcasesPatIdent #[Syntax.mkSimpleIdent (Name.simple "this")])
            | _ =>
              rcasesPatStep true 32 ctx s
          let s := optionalFn (seqFn (symbolFn ":") term0) ctx s
          let s := symbolFn ":=" ctx s
          let s := term0 ctx s
          s.mkNode SyntaxKind.tacticObtain iniSz
        | "calc" =>
          let s := tokenFn ctx s
          let s := calcStepsFn termRec ctx s
          s.mkNode SyntaxKind.tacticCalc iniSz
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
        | "decide" | "native_decide" =>
          let s := tokenFn ctx s
          s.mkNode SyntaxKind.tacticDecide iniSz
        | "norm_num" =>
          let s := tokenFn ctx s
          let s := optionalFn (seqFn (nonReservedSymbolFn "at") identFn) ctx s
          s.mkNode SyntaxKind.tacticNormNum iniSz
        | "ring" | "ring_nf" =>
          let s := tokenFn ctx s
          s.mkNode SyntaxKind.tacticRing iniSz
        | "omega" | "linarith" =>
          let s := tokenFn ctx s
          s.mkNode SyntaxKind.tacticOmega iniSz
        | "assumption" =>
          let s := tokenFn ctx s
          s.mkNode SyntaxKind.tacticAssumption iniSz
        | "trivial" =>
          let s := tokenFn ctx s
          s.mkNode SyntaxKind.tacticTrivial iniSz
        | "contradiction" =>
          let s := tokenFn ctx s
          s.mkNode SyntaxKind.tacticContradiction iniSz
        | "exfalso" =>
          let s := tokenFn ctx s
          s.mkNode SyntaxKind.tacticExfalso iniSz
        | "done" =>
          let s := tokenFn ctx s
          s.mkNode SyntaxKind.tacticDone iniSz
        | "constructor" =>
          let s := tokenFn ctx s
          s.mkNode SyntaxKind.tacticConstructor iniSz
        | "left" =>
          let s := tokenFn ctx s
          s.mkNode SyntaxKind.tacticLeft iniSz
        | "right" =>
          let s := tokenFn ctx s
          s.mkNode SyntaxKind.tacticRight iniSz
        | "split" =>
          let s := tokenFn ctx s
          s.mkNode SyntaxKind.tacticSplit iniSz
        | "exists" | "use" =>
          let s := tokenFn ctx s
          let s := sepBy1Fn term0 (symbolFn ",") false ctx s
          s.mkNode SyntaxKind.tacticExists iniSz
        | "symm" | "symmetry" =>
          let s := tokenFn ctx s
          s.mkNode SyntaxKind.tacticSymm iniSz
        | "trans" | "transitivity" =>
          let s := tokenFn ctx s
          let s := optionalFn sameLineTerm0 ctx s
          s.mkNode SyntaxKind.tacticTrans iniSz
        | "congr" =>
          let s := tokenFn ctx s
          s.mkNode SyntaxKind.tacticCongr iniSz
        | "funext" =>
          let s := tokenFn ctx s
          let s := manyFn sameLineBinderIdent ctx s
          s.mkNode SyntaxKind.tacticFunext iniSz
        | "ext" =>
          let s := tokenFn ctx s
          let s := manyFn sameLineBinderIdent ctx s
          s.mkNode SyntaxKind.tacticExt iniSz
        | "sorry" | "admit" =>
          let s := tokenFn ctx s
          s.mkNode SyntaxKind.tacticSorry iniSz
        | "show" =>
          let s := tokenFn ctx s
          let s := term0 ctx s
          s.mkNode SyntaxKind.tacticShow iniSz
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
          let s := optionalFn (seqFn (nonReservedSymbolFn "at") identFn) ctx s
          s.mkNode SyntaxKind.tacticRw iniSz
        | "simp" =>
          let s := tokenFn ctx s
          let s := optionalFn (nonReservedSymbolFn "only") ctx s
          let s := optionalFn (fun c st =>
            (symbolFn "[" c st).bindState fun st =>
              if st.hasError then st else
              let rRule : ParserFn := fun c2 st2 =>
                let rSz := st2.stackSize
                let st2 := optionalFn (orelseFn (symbolFn "←") (symbolFn "<-")) c2 st2
                let st2 := term0 c2 st2
                st2.mkNode SyntaxKind.tacticRwRule rSz
              let st := sepByFn rRule (symbolFn ",") false c st
              if st.hasError then st else
              symbolFn "]" c st) ctx s
          let s := optionalFn (seqFn (nonReservedSymbolFn "at") identFn) ctx s
          s.mkNode SyntaxKind.tacticSimp iniSz
        | "dsimp" =>
          let s := tokenFn ctx s
          let s := optionalFn (nonReservedSymbolFn "only") ctx s
          let s := optionalFn (fun c st =>
            (symbolFn "[" c st).bindState fun st =>
              if st.hasError then st else
              let rRule : ParserFn := fun c2 st2 =>
                let rSz := st2.stackSize
                let st2 := optionalFn (orelseFn (symbolFn "←") (symbolFn "<-")) c2 st2
                let st2 := term0 c2 st2
                st2.mkNode SyntaxKind.tacticRwRule rSz
              let st := sepByFn rRule (symbolFn ",") false c st
              if st.hasError then st else
              symbolFn "]" c st) ctx s
          let s := optionalFn (seqFn (nonReservedSymbolFn "at") identFn) ctx s
          s.mkNode SyntaxKind.tacticDSimp iniSz
        | "have" =>
          let s := tokenFn ctx s
          let (tNext?, s) := peekToken ctx s
          let s := match tNext? with
            | some (.atom _ ":") | some (.atom _ ":=") =>
              s.pushSyntax (Syntax.mkSimpleIdent (Name.simple "this"))
            | _ =>
              binderIdentFn ctx s
          let s := optionalFn (seqFn (symbolFn ":") term0) ctx s
          let s := symbolFn ":=" ctx s
          let s := term0 ctx s
          s.mkNode SyntaxKind.tacticHave iniSz
        | "let" =>
          let s := tokenFn ctx s
          let (tNext?, s) := peekToken ctx s
          let s := match tNext? with
            | some (.atom _ ":") | some (.atom _ ":=") =>
              s.pushSyntax (Syntax.mkSimpleIdent (Name.simple "this"))
            | _ =>
              binderIdentFn ctx s
          let s := optionalFn (seqFn (symbolFn ":") term0) ctx s
          let s := symbolFn ":=" ctx s
          let s := term0 ctx s
          s.mkNode SyntaxKind.tacticLet iniSz
        | "suffices" =>
          let s := tokenFn ctx s
          let namedSuff : ParserFn := fun c st =>
            (binderIdentFn c st).bindState fun st =>
              if st.hasError then st else
              symbolFn ":" c st
          let anonSuff : ParserFn := fun c st =>
            let st := st.pushSyntax (Syntax.mkSimpleIdent (Name.simple "this"))
            let (t?, st) := peekToken c st
            match t? with
            | some (.atom _ ":") => tokenFn c st
            | _ => st.pushSyntax (Syntax.mkSimpleAtom ":")
          let s := tryOrElseFn namedSuff anonSuff ctx s
          let s := term0 ctx s
          if s.hasError then s else
          let (modeTok?, s) := peekToken ctx s
          let s := match modeTok? with
            | some (.atom _ "by") | some (.ident _ _ (.str (.anonymous _) "by" _) _) =>
              let s := tokenFn ctx s
              tacticSeqCore termRec stopAtFocus true fuel ctx s
            | some (.ident _ _ (.str (.anonymous _) "from" _) _) | some (.atom _ "from") =>
              let s := tokenFn ctx s
              term0 ctx s
            | _ =>
              s.mkUnexpectedError "expected 'by' or 'from' in 'suffices' tactic"
          s.mkNode SyntaxKind.tacticSuffices iniSz
        | "specialize" =>
          let s := tokenFn ctx s
          let s := identFn ctx s
          let s := manyFn sameLineTermArg ctx s
          s.mkNode SyntaxKind.tacticSpecialize iniSz
        | "clear" =>
          let s := tokenFn ctx s
          let s := many1Fn sameLineIdent ctx s
          s.mkNode SyntaxKind.tacticClear iniSz
        | "revert" =>
          let s := tokenFn ctx s
          let s := many1Fn sameLineIdent ctx s
          s.mkNode SyntaxKind.tacticRevert iniSz
        | "generalize" =>
          let s := tokenFn ctx s
          let namedGen : ParserFn := fun c st =>
            (identFn c st).bindState fun st =>
              if st.hasError then st else
              (symbolFn ":" c st).bindState fun st =>
                if st.hasError then st else
                st.popSyntax
          let unnamedGen : ParserFn := fun _ st =>
            st.pushSyntax (Syntax.mkSimpleIdent Name.mkAnon)
          let s := tryOrElseFn namedGen unnamedGen ctx s
          let s := withPrecFn 51 termRec ctx s
          let s := symbolFn "=" ctx s
          let s := identFn ctx s
          s.mkNode SyntaxKind.tacticGeneralize iniSz
        | "subst" =>
          let s := tokenFn ctx s
          let s := many1Fn sameLineIdent ctx s
          s.mkNode SyntaxKind.tacticSubst iniSz
        | "by_cases" =>
          let s := tokenFn ctx s
          let namedByCases : ParserFn := fun c st =>
            (identFn c st).bindState fun st =>
              if st.hasError then st else
              (symbolFn ":" c st).bindState fun st =>
                if st.hasError then st else
                let st := st.popSyntax
                term0 c st
          let unnamedByCases : ParserFn := fun c st =>
            let st := st.pushSyntax (Syntax.mkSimpleIdent (Name.simple "h"))
            term0 c st
          let s := tryOrElseFn namedByCases unnamedByCases ctx s
          s.mkNode SyntaxKind.tacticByCases iniSz
        | "by_contra" | "by_contradiction" =>
          let s := tokenFn ctx s
          let (nextT?, s) := peekToken ctx s
          let s := match nextT? with
            | some tok =>
              if !hasLeadingNewline tok then
                match tok with
                | .ident .. | .atom _ "_" => binderIdentFn ctx s
                | _ => s.pushSyntax (Syntax.mkSimpleIdent (Name.simple "this"))
              else
                s.pushSyntax (Syntax.mkSimpleIdent (Name.simple "this"))
            | none =>
              s.pushSyntax (Syntax.mkSimpleIdent (Name.simple "this"))
          s.mkNode SyntaxKind.tacticByContra iniSz
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
          match tryLeadNotationRules termRec kw ctx.env.notations ctx s with
          | some sHit => sHit
          | none      => s.mkUnexpectedError s!"expected tactic, got '{kw}'"
      | _ =>
        s.mkUnexpectedError "expected tactic"
    let stepTactic : ParserFn := fun ctx s =>
      let iniSz := s.stackSize
      let s := oneTactic ctx s
      if s.hasError then s else
      let (nextTok?, s) := peekToken ctx s
      match nextTok? with
      | some (.atom _ "<;>") =>
        let s := tokenFn ctx s
        let s := tacticSeqCore termRec stopAtFocus true fuel ctx s
        s.mkNode SyntaxKind.tacticAndThen iniSz
      | _ => s
    if singleStep then
      stepTactic
    else
      fun ctx s =>
        let iniSz := s.stackSize
        let s := stepTactic ctx s
        if s.hasError then s else
        let s := manyLoop (fun c st =>
          let st := optionalFn (symbolFn ";") c st
          let st := st.popSyntax
          if stopAtFocus then
            let (t?, st) := peekToken c st
            if isFocusOrCaseToken t? then
              st.mkUnexpectedError "end of focused tactic block"
            else
              stepTactic c st
          else
            stepTactic c st) ctx s (ctx.inputCtx.size - s.pos + 1)
        s.mkNode SyntaxKind.tacticSeq iniSz

/-- Parse a tactic sequence, structurally recursive on `fuel : Nat`. -/
def tacticSeqStep (termRec : ParserFn) (fuel : Nat) : ParserFn :=
  tacticSeqCore termRec false false fuel

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

/-- Attach `bVPref` and `bTy` to untyped `explicitBinder` nodes in a `∀ a b c : T, body` binder list. -/
def attachTypeToBinders (bVPref bTy : Ix.Syntax) : List Ix.Syntax → List Ix.Syntax
  | [] => []
  | b :: bs =>
    let b' := match b with
      | .node info k ⟨[p0, p1, _, p3]⟩ =>
        if k == SyntaxKind.explicitBinder && Syntax.isNone p3 then
          .node info SyntaxKind.explicitBinder #[p0, p1, bVPref, bTy]
        else b
      | _ => b
    b' :: attachTypeToBinders bVPref bTy bs

/-- Extract any parenthesized bounded binder conditions `(x > 0)` from `binders`,
    returning `(cleanedBinders, boundConds)`. -/
def extractBinderBounds : List Ix.Syntax → List Ix.Syntax × List Ix.Syntax
  | [] => ([], [])
  | b :: bs =>
    let (bs', restConds) := extractBinderBounds bs
    match b with
    | .node info k ⟨[bPref, idsNode, vPref, .node _ bk ⟨[.atom _ "_bound", opTok, rhsStx]⟩]⟩ =>
      if k == SyntaxKind.explicitBinder && bk == SyntaxKind.binOpTerm then
        let bClean := .node info SyntaxKind.explicitBinder #[bPref, idsNode, vPref, Syntax.mkNullNode #[]]
        let newConds := (Syntax.getArgs idsNode).toList.map fun idStx =>
          Syntax.mkNode SyntaxKind.binOpTerm #[idStx, opTok, rhsStx]
        (bClean :: bs', newConds ++ restConds)
      else
        (b :: bs', restConds)
    | _ => (b :: bs', restConds)

/-- Build relational bound conditions `id opTok boundRhs` for all untyped `explicitBinder`s in `binders`. -/
def mkUnparenBoundConds (opTok boundRhs : Ix.Syntax) : List Ix.Syntax → List Ix.Syntax
  | [] => []
  | b :: bs =>
    let here := match b with
      | .node _ k ⟨[_, idsNode, _, tyNode]⟩ =>
        if k == SyntaxKind.explicitBinder && Syntax.isNone tyNode then
          (Syntax.getArgs idsNode).toList.map fun idStx =>
            Syntax.mkNode SyntaxKind.binOpTerm #[idStx, opTok, boundRhs]
        else []
      | _ => []
    here ++ mkUnparenBoundConds opTok boundRhs bs

/-- Expand a single binder node (`explicitBinder`, etc.) into one single-variable binder per identifier. -/
def expandSingleBinders (bStx : Ix.Syntax) : List Ix.Syntax :=
  match bStx with
  | .node info k ⟨[bPref, idsNode, vPref, tyNode]⟩ =>
    if k == SyntaxKind.explicitBinder || k == SyntaxKind.implicitBinder ||
       k == SyntaxKind.strictImplicitBinder || k == SyntaxKind.instBinder then
      (Syntax.getArgs idsNode).toList.map fun idStx =>
        Syntax.mkNode SyntaxKind.explicitBinder #[bPref, Syntax.mkNullNode #[idStx], vPref, tyNode] info
    else
      [bStx]
  | _ => [bStx]

/-- Desugar `∃ b₁ ... bₙ, body` into nested `Exists (fun b₁ => ... (Exists (fun bₙ => body)))`. -/
def mkExistsFromBinders (binders : List Ix.Syntax) (body : Ix.Syntax) : Ix.Syntax :=
  let singleBinders := binders.flatMap expandSingleBinders
  singleBinders.foldr (fun b acc =>
    let lam := Syntax.mkNode SyntaxKind.funTerm
      #[Syntax.mkSimpleAtom "fun", Syntax.mkNullNode #[b], Syntax.mkSimpleAtom "=>", acc]
    Syntax.mkNode SyntaxKind.appTerm #[Syntax.mkSimpleIdent (Name.simple "Exists"), lam]
  ) body

/-- Replace every `.atom _ "·"` in `stx` (stopping at `byTactic` blocks) with fresh parameter
    identifiers `_cd_0`, `_cd_1`, ... and return `(rewrittenStx, paramNames, nextIdx)`. -/
def replaceCenterDots : Nat → Ix.Syntax → Nat → Ix.Syntax × List Ix.Name × Nat
  | 0, stx, nextIdx => (stx, [], nextIdx)
  | fuel + 1, stx, nextIdx =>
    match stx with
    | .atom info "·" =>
      let paramName := Name.simple s!"_cd_{nextIdx}"
      let idStx := Syntax.mkIdent info ⟨"_cd", 0, 3⟩ paramName
      (idStx, [paramName], nextIdx + 1)
    | .node info kind args =>
      if kind == SyntaxKind.byTactic then
        (stx, [], nextIdx)
      else
        let rec loopArgs : List Ix.Syntax → List Ix.Syntax → List Ix.Name → Nat →
            List Ix.Syntax × List Ix.Name × Nat
          | [], revStxs, revNames, idx => (revStxs.reverse, revNames.reverse, idx)
          | a :: as, revStxs, revNames, idx =>
            let (a', nms, idx') := replaceCenterDots fuel a idx
            loopArgs as (a' :: revStxs) (nms.reverse ++ revNames) idx'
        let (newArgs, paramNames, nextIdx') := loopArgs args.toList [] [] nextIdx
        if paramNames.isEmpty then
          (stx, [], nextIdx)
        else
          (.node info kind (Array.mk newArgs), paramNames, nextIdx')
    | _ => (stx, [], nextIdx)

/-- If `stx` contains any centered-dot placeholders `·`, wrap it in `fun _cd_0 _cd_1 ... => stx'`. -/
def expandCenterDots (stx : Ix.Syntax) : Ix.Syntax :=
  let (body', paramNames, _) := replaceCenterDots 128 stx 0
  if paramNames.isEmpty then
    stx
  else
    let emptyPref := Syntax.mkNode SyntaxKind.binderPrefix #[]
    let emptyVPref := Syntax.mkNode SyntaxKind.valuePrefix #[]
    let binderNodes := paramNames.map fun nm =>
      Syntax.mkNode SyntaxKind.explicitBinder
        #[emptyPref, Syntax.mkNullNode #[Syntax.mkSimpleIdent nm], emptyVPref, Syntax.mkNullNode #[]]
    Syntax.mkNode SyntaxKind.funTerm
      #[Syntax.mkSimpleAtom "fun", Syntax.mkNullNode (Array.mk binderNodes),
        Syntax.mkSimpleAtom "=>", body']

/-- Parse a leading expression (atoms, binders, `fun`, `forall`, `∃`, `let`, `let borrow`, `if`, `match`, `by`, `calc`). -/
def leadTermFn (termRec : ParserFn) (tacticFuel : Nat) : ParserFn := fun ctx s =>
  let term0 := withPrecFn 0 termRec
  let parseSyntaxQuoteBody : ParserFn := fun c st =>
    let tryCatPrefix : ParserFn := fun c2 st2 =>
      (identFn c2 st2).bindState fun st2 =>
        if st2.hasError then st2 else
        (symbolFn "|" c2 st2).bindState fun st2 =>
          if st2.hasError then st2 else
          st2.popSyntax
    let noCatPrefix : ParserFn := fun _ st2 =>
      st2.pushSyntax (Syntax.mkSimpleIdent Name.mkAnon)
    (tryOrElseFn tryCatPrefix noCatPrefix c st).bindState fun st =>
      let catId := Syntax.getId st.stxStack.back
      let st := st.popSyntax
      if catId == Name.simple "tactic" then
        tryOrElseFn (tacticSeqCore termRec false true tacticFuel) term0 c st
      else
        term0 c st
  bindPeek ctx s fun tok? s =>
    let leadNotationHit? : Option ParserState :=
      match ctx.env.notations, tok? with
      | [], _ | _, none => none
      | nots, some tok =>
        let tStr := tokenText tok
        if tStr.isEmpty then none
        else tryLeadNotationRules termRec tStr nots ctx s
    match leadNotationHit? with
    | some sHit => sHit
    | none =>
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
        | "·" =>
          tokenFn ctx s
        | "$" =>
          let iniSz := s.stackSize
          (symbolFn "$" ctx s).bindState fun s =>
            bindPeek ctx s fun next? s =>
              match next? with
              | some (.atom _ "(") =>
                (symbolFn "(" ctx s).bindState fun s =>
                (identFn ctx s).bindState fun s =>
                (symbolFn ")" ctx s).bindState fun s =>
                  if s.hasError then s else
                  let idStx := s.stxStack.getD (iniSz + 2)
                  let s := s.shrinkStack (iniSz + 1)
                  (s.pushSyntax idStx).mkNode SyntaxKind.antiquotTerm iniSz
              | _ =>
                (identFn ctx s).bindState fun s =>
                  s.mkNode SyntaxKind.antiquotTerm iniSz
        | "`(" =>
          let iniSz := s.stackSize
          (symbolFn "`(" ctx s).bindState fun s =>
          (parseSyntaxQuoteBody ctx s).bindState fun s =>
            if s.hasError then s else
            let inner := s.stxStack.back
            (symbolFn ")" ctx s).bindState fun s =>
              if s.hasError then s else
              let s := s.shrinkStack iniSz
              s.pushSyntax inner
        | "`" =>
          let iniSz := s.stackSize
          (symbolFn "`" ctx s).bindState fun s =>
            bindPeek ctx s fun next? s =>
              match next? with
              | some (.atom _ "(") =>
                (symbolFn "(" ctx s).bindState fun s =>
                (parseSyntaxQuoteBody ctx s).bindState fun s =>
                  if s.hasError then s else
                  let inner := s.stxStack.back
                  (symbolFn ")" ctx s).bindState fun s =>
                    if s.hasError then s else
                    let s := s.shrinkStack iniSz
                    s.pushSyntax inner
              | _ =>
                (withPrecFn maxPrec termRec ctx s).bindState fun s =>
                  if s.hasError then s else
                  let inner := s.stxStack.back
                  let s := s.shrinkStack iniSz
                  s.pushSyntax inner
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
        | "forall" | "∀" | "∃" =>
          let isExists := sym == "∃"
          let iniSz := s.stackSize
          (tokenFn ctx s).bindState fun s =>
          (many1Fn (simpleOrBracketedBinderFn termRec) ctx s).bindState fun s =>
            if s.hasError then s else
            let finishQuantifier (sFinal : ParserState) (extraConds : List Ix.Syntax) : ParserState :=
              if sFinal.hasError then sFinal else
              match sFinal.stxStack.rev with
              | bodyStx :: vPref :: commaTok :: bindersNode :: kwTok :: restRev =>
                let (cleanBinders, parenConds) := extractBinderBounds (Syntax.getArgs bindersNode).toList
                let allConds := parenConds ++ extraConds
                let emptyVPref := Syntax.mkNode SyntaxKind.valuePrefix #[]
                if isExists then
                  let bodyWithConds := allConds.foldr (fun c acc =>
                    Syntax.mkNode SyntaxKind.binOpTerm #[c, Syntax.mkSimpleAtom "∧", acc]) bodyStx
                  let exStx := mkExistsFromBinders cleanBinders bodyWithConds
                  SyntaxStack.bindList restRev fun restRev' =>
                  InputContext.bindNat (iniSz + 1) fun newLen =>
                    ⟨⟨exStx :: restRev', newLen⟩, sFinal.lhsPrec, sFinal.pos, sFinal.cache, sFinal.errorMsg⟩
                else
                  let bodyWithConds := allConds.foldr (fun c acc =>
                    Syntax.mkNode SyntaxKind.arrowTerm #[c, Syntax.mkSimpleAtom "→", emptyVPref, acc]) bodyStx
                  let newBinders := Syntax.mkNullNode (Array.mk cleanBinders)
                  let forallNode := Syntax.mkNode SyntaxKind.forallTerm
                    #[kwTok, newBinders, commaTok, vPref, bodyWithConds]
                  SyntaxStack.bindList restRev fun restRev' =>
                  InputContext.bindNat (iniSz + 1) fun newLen =>
                    ⟨⟨forallNode :: restRev', newLen⟩, sFinal.lhsPrec, sFinal.pos, sFinal.cache, sFinal.errorMsg⟩
              | _ => sFinal.mkNode SyntaxKind.forallTerm iniSz
            bindPeek ctx s fun sepTok? s =>
              match sepTok? with
              | some (.atom _ ":") =>
                (symbolFn ":" ctx s).bindState fun s =>
                (valuePrefixFn ctx s).bindState fun s =>
                (term0 ctx s).bindState fun s =>
                  if s.hasError then s else
                  bindPeek ctx s fun afterTyTok? s =>
                    match afterTyTok? with
                    | some (.atom _ ",") =>
                      let s := match s.stxStack.rev with
                        | bTy :: bVPref :: _ :: bindersNode :: kwTok :: restRev =>
                          let updatedList := attachTypeToBinders bVPref bTy (Syntax.getArgs bindersNode).toList
                          SyntaxStack.bindList updatedList fun updatedList' =>
                          InputContext.bindNat (iniSz + 2) fun newLen =>
                            let newBinders := Syntax.mkNullNode (Array.mk updatedList')
                            ⟨⟨newBinders :: kwTok :: restRev, newLen⟩, s.lhsPrec, s.pos, s.cache, s.errorMsg⟩
                        | _ => s
                      (symbolFn "," ctx s).bindState fun s =>
                      (valuePrefixFn ctx s).bindState fun s =>
                      (term0 ctx s).bindState fun s =>
                        finishQuantifier s []
                    | _ =>
                      finishQuantifier s []
              | some (.atom _ relSym) =>
                if isBinderRelOp relSym then
                  (tokenFn ctx s).bindState fun s =>
                    let opTok := s.stxStack.back
                    let s := s.popSyntax
                    (term0 ctx s).bindState fun s =>
                      if s.hasError then s else
                      let boundRhs := s.stxStack.back
                      let s := s.popSyntax
                      let bindersNode := s.stxStack.back
                      let extraConds := mkUnparenBoundConds opTok boundRhs (Syntax.getArgs bindersNode).toList
                      (symbolFn "," ctx s).bindState fun s =>
                      (valuePrefixFn ctx s).bindState fun s =>
                      (term0 ctx s).bindState fun s =>
                        finishQuantifier s extraConds
                else
                  (symbolFn "," ctx s).bindState fun s =>
                  (valuePrefixFn ctx s).bindState fun s =>
                  (term0 ctx s).bindState fun s =>
                    finishQuantifier s []
              | _ =>
                (symbolFn "," ctx s).bindState fun s =>
                (valuePrefixFn ctx s).bindState fun s =>
                (term0 ctx s).bindState fun s =>
                  finishQuantifier s []
        | "let" =>
          let iniSz := s.stackSize
          (symbolFn "let" ctx s).bindState fun s =>
            bindPeek ctx s fun afterLet? s =>
              let isBorrow := match afterLet? with
                | some (.ident _ _ (.str (.anonymous _) "borrow" _) _) => true
                | _ => false
              let isRec := match afterLet? with
                | some (.ident _ _ (.str (.anonymous _) "rec" _) _) | some (.atom _ "rec") => true
                | _ => false
              let sSubKw :=
                if isBorrow then nonReservedSymbolFn "borrow" ctx s
                else if isRec then nonReservedSymbolFn "rec" ctx s
                else s
              sSubKw.bindState fun s =>
              (binderPrefixFn ctx s).bindState fun s =>
                bindPeek ctx s fun patTok? s =>
                  match patTok? with
                  | some (.atom _ "⟨") =>
                    let patSz := s.stackSize
                    (symbolFn "⟨" ctx s).bindState fun s =>
                    (sepByFn term0 (symbolFn ",") true ctx s).bindState fun s =>
                    (symbolFn "⟩" ctx s).bindState fun s =>
                    (s.mkNode SyntaxKind.anonCtor patSz).bindState fun s =>
                      if s.hasError then s else
                      let anonPat := s.stxStack.back
                      let s := s.popSyntax
                      (optionalFn (fun c st =>
                        (symbolFn ":" c st).bindState fun st =>
                          if st.hasError then st else
                          (valuePrefixFn c st).bindState fun st =>
                            term0 c st) ctx s).bindState fun s =>
                        if s.hasError then s else
                        let optTyNode := s.stxStack.back
                        let s := s.popSyntax
                        (symbolFn ":=" ctx s).bindState fun s =>
                        (term0 ctx s).bindState fun s =>
                          if s.hasError then s else
                          let valStx := s.stxStack.back
                          let s := s.popSyntax
                          (optionalFn (orelseFn (symbolFn ";") (symbolFn "in")) ctx s).bindState fun s =>
                          (term0 ctx s).bindState fun s =>
                            if s.hasError then s else
                            let bodyStx := s.stxStack.back
                            let s := s.shrinkStack iniSz
                            let discrStx :=
                              if Nat.ble 3 (Syntax.getNumArgs optTyNode) then
                                Syntax.mkNode SyntaxKind.typeAscription
                                  #[Syntax.mkSimpleAtom "(", valStx, Syntax.mkSimpleAtom ":",
                                    Syntax.getArg optTyNode 1, Syntax.getArg optTyNode 2, Syntax.mkSimpleAtom ")"]
                              else valStx
                            let altNode := Syntax.mkNode SyntaxKind.matchAlt
                              #[Syntax.mkSimpleAtom "|", Syntax.mkNullNode #[anonPat],
                                Syntax.mkSimpleAtom "=>", bodyStx]
                            let matchNode := Syntax.mkNode SyntaxKind.matchTerm
                              #[Syntax.mkSimpleAtom "match", Syntax.mkNullNode #[discrStx],
                                Syntax.mkSimpleAtom "with", Syntax.mkNullNode #[altNode]]
                            s.pushSyntax matchNode
                  | _ =>
                    (binderIdentFn ctx s).bindState fun s =>
                      if s.hasError then s else
                      (manyFn (simpleOrBracketedBinderFn termRec) ctx s).bindState fun s =>
                      (optionalFn (fun c st =>
                        (symbolFn ":" c st).bindState fun st =>
                          if st.hasError then st else
                          (valuePrefixFn c st).bindState fun st =>
                            term0 c st) ctx s).bindState fun s =>
                        if s.hasError then s else
                        bindPeek ctx s fun rhsTok? s =>
                          let sAfterRhs := match rhsTok? with
                            | some (.atom _ "|") =>
                              if isRec then
                                let s := s.pushSyntax (Syntax.mkSimpleAtom ":=")
                                many1Fn (matchAltFn termRec) ctx s
                              else
                                symbolFn ":=" ctx s
                            | _ =>
                              (symbolFn ":=" ctx s).bindState fun s =>
                                if s.hasError then s else term0 ctx s
                          sAfterRhs.bindState fun s =>
                            if s.hasError then s else
                            (optionalFn (orelseFn (symbolFn ";") (symbolFn "in")) ctx s).bindState fun s =>
                            (term0 ctx s).bindState fun s =>
                              let nodeKind :=
                                if isBorrow then SyntaxKind.letBorrowTerm
                                else if isRec then SyntaxKind.letRecTerm
                                else SyntaxKind.letTerm
                              s.mkNode nodeKind iniSz
        | "have" =>
          let iniSz := s.stackSize
          (symbolFn "have" ctx s).bindState fun s =>
            bindPeek ctx s fun patTok? s =>
              match patTok? with
              | some (.atom _ "⟨") =>
                let patSz := s.stackSize
                (symbolFn "⟨" ctx s).bindState fun s =>
                (sepByFn term0 (symbolFn ",") true ctx s).bindState fun s =>
                (symbolFn "⟩" ctx s).bindState fun s =>
                (s.mkNode SyntaxKind.anonCtor patSz).bindState fun s =>
                  if s.hasError then s else
                  let anonPat := s.stxStack.back
                  let s := s.popSyntax
                  (optionalFn (seqFn (symbolFn ":") term0) ctx s).bindState fun s =>
                    if s.hasError then s else
                    let optTyNode := s.stxStack.back
                    let s := s.popSyntax
                    (symbolFn ":=" ctx s).bindState fun s =>
                    (term0 ctx s).bindState fun s =>
                      if s.hasError then s else
                      let valStx := s.stxStack.back
                      let s := s.popSyntax
                      (optionalFn (orelseFn (symbolFn ";") (symbolFn "in")) ctx s).bindState fun s =>
                      (term0 ctx s).bindState fun s =>
                        if s.hasError then s else
                        let bodyStx := s.stxStack.back
                        let s := s.shrinkStack iniSz
                        let discrStx :=
                          if Nat.ble 2 (Syntax.getNumArgs optTyNode) then
                            Syntax.mkNode SyntaxKind.typeAscription
                              #[Syntax.mkSimpleAtom "(", valStx, Syntax.mkSimpleAtom ":",
                                Syntax.mkNode SyntaxKind.valuePrefix #[],
                                Syntax.getArg optTyNode 1, Syntax.mkSimpleAtom ")"]
                          else valStx
                        let altNode := Syntax.mkNode SyntaxKind.matchAlt
                          #[Syntax.mkSimpleAtom "|", Syntax.mkNullNode #[anonPat],
                            Syntax.mkSimpleAtom "=>", bodyStx]
                        let matchNode := Syntax.mkNode SyntaxKind.matchTerm
                          #[Syntax.mkSimpleAtom "match", Syntax.mkNullNode #[discrStx],
                            Syntax.mkSimpleAtom "with", Syntax.mkNullNode #[altNode]]
                        s.pushSyntax matchNode
              | _ =>
                let sAfterId := match patTok? with
                  | some (.atom _ ":") | some (.atom _ ":=") =>
                    s.pushSyntax (Syntax.mkSimpleIdent (Name.simple "this"))
                  | _ =>
                    binderIdentFn ctx s
                sAfterId.bindState fun s =>
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
              (binderIdentFn c st).bindState fun st =>
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
        | "calc" =>
          let iniSz := s.stackSize
          (symbolFn "calc" ctx s).bindState fun s =>
            if s.hasError then s else
            let calcTok := s.stxStack.back
            (calcStepsFn termRec ctx s).bindState fun s =>
              if s.hasError then s else
              let stepsNode := s.stxStack.back
              let s := s.shrinkStack iniSz
              let tacNode := Syntax.mkNode SyntaxKind.tacticCalc #[calcTok, stepsNode]
              s.pushSyntax (Syntax.mkNode SyntaxKind.byTactic #[calcTok, tacNode])
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
                        (st.mkNode SyntaxKind.tupleTerm pSz).bindState fun st =>
                          if st.hasError then st else
                          let tup := expandCenterDots st.stxStack.back
                          let st := st.shrinkStack pSz
                          st.pushSyntax tup
                      | _ =>
                        let inner := expandCenterDots st.stxStack.back
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
                  (symbolFn "with" c2 st2).bindState fun st2 =>
                    if st2.hasError then st2 else st2.popSyntax
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
          match findPrefixOp? ctx.env sym with
          | some op =>
            (tokenFn ctx s).bindState fun s =>
              let s := s.popSyntax
              (withPrecFn op.prec termRec ctx s).bindState fun s =>
                if s.hasError then s else
                match op.targetFn with
                | some fnName =>
                  let argStx := s.stxStack.back
                  let s := s.popSyntax
                  s.pushSyntax (Syntax.mkNode SyntaxKind.appTerm #[Syntax.mkSimpleIdent fnName, argStx])
                | none => s
          | none =>
            s.mkUnexpectedError s!"unexpected token '{sym}' in term"
      | _ =>
        s.mkUnexpectedError "expected term"

/-- Pratt trailing loop: handles `.field` / `.0` projections, function application `f a`,
    substructural function arrows `A → !B`, and binary infix / postfix operators. -/
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
          let trailNotationHit? : Option ParserState :=
            match ctx.env.notations with
            | [] => none
            | nots =>
              let tStr := tokenText tok
              if tStr.isEmpty then none
              else tryTrailNotationRules termRec tStr nots ctx s
          match trailNotationHit? with
          | some sHit => trailingTermLoop termRec ctx sHit fuel
          | none =>
            match tok with
            | .atom _ sym =>
              -- 1. Field or index projection `.field` / `.0` (tightest binding, `maxPrec`)
              if sym == "." && Nat.ble (ctx.prec + 1) maxPrec then
                let iniSz := s.stackSize
                (symbolFn "." ctx s).bindState fun s =>
                (orelseFn identFn numLitFn ctx s).bindState fun s =>
                  if s.hasError then s else
                  (s.mkTrailingNode SyntaxKind.projTerm iniSz maxPrec).bindState fun s =>
                    trailingTermLoop termRec ctx s fuel
              -- 2. Non-dependent function arrow `A → !B` / `A -> ~B` (precedence `arrowPrec := 25`, right-assoc)
              else if (sym == "→" || sym == "->") && Nat.ble ctx.prec arrowPrec then
                let iniSz := s.stackSize
                (tokenFn ctx s).bindState fun s =>
                (valuePrefixFn ctx s).bindState fun s =>
                (withPrecFn arrowPrec termRec ctx s).bindState fun s =>
                  if s.hasError then s else
                  (s.mkTrailingNode SyntaxKind.arrowTerm iniSz arrowPrec).bindState fun s =>
                    trailingTermLoop termRec ctx s fuel
              -- 3. Registered binary infix operator
              else
                match findInfixOp? ctx.env sym ctx.prec with
                | some op =>
                  let iniSz := s.stackSize
                  (tokenFn ctx s).bindState fun s =>
                    let rhsMinPrec := match op.fixity with
                      | .infixl => op.prec + 1
                      | .infixr => op.prec
                      | _       => op.prec + 1
                    (withPrecFn rhsMinPrec termRec ctx s).bindState fun s =>
                      if s.hasError then s else
                      let sNext :=
                        if op.kind == SyntaxKind.appTerm then
                          match op.targetFn with
                          | some fnName =>
                            let rhsStx := s.stxStack.back
                            let s1 := s.shrinkStack (iniSz - 1)
                            let lhsStx := s.stxStack.getD (iniSz - 1)
                            let app1 := Syntax.mkNode SyntaxKind.appTerm #[Syntax.mkSimpleIdent fnName, lhsStx]
                            let app2 := Syntax.mkNode SyntaxKind.appTerm #[app1, rhsStx]
                            s1.pushSyntax app2
                          | none => s.mkTrailingNode op.kind iniSz op.prec
                        else
                          s.mkTrailingNode op.kind iniSz op.prec
                      sNext.bindState fun s =>
                        trailingTermLoop termRec ctx s fuel
                | none =>
                  match findPostfixOp? ctx.env sym ctx.prec with
                  | some op =>
                    let iniSz := s.stackSize
                    (tokenFn ctx s).bindState fun s =>
                      let sNext := match op.targetFn with
                        | some fnName =>
                          let lhsStx := s.stxStack.getD (iniSz - 1)
                          let s1 := s.shrinkStack (iniSz - 1)
                          s1.pushSyntax (Syntax.mkNode SyntaxKind.appTerm #[Syntax.mkSimpleIdent fnName, lhsStx])
                        | none => s
                      sNext.bindState fun s =>
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
            | _ =>
              -- Non-atom token (`.ident` or literal `.node`): skip operator lookups and check juxtaposition directly
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
