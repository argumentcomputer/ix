/-
  Ix.Frontend.Parser.Basic: Pure, total lexer and parser combinators for the Ix Frontend.
  Every scanner and combinator is structurally total (no `partial`, `unsafe`, or `IO`).
-/
module

public import Ix.Frontend.Parser.Types

@[expose] public section

namespace Ix.Frontend.Parser

/-! ## Character Predicates & Whitespace / Comment Scanners -/

def isSpaceChar (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '\r' || c == '\n'

def isDigitChar (c : Char) : Bool :=
  '0' ≤ c && c ≤ '9'

def isHexDigitChar (c : Char) : Bool :=
  ('0' ≤ c && c ≤ '9') || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F')

def hexDigitVal (c : Char) : Nat :=
  if '0' ≤ c && c ≤ '9' then c.toNat - '0'.toNat
  else if 'a' ≤ c && c ≤ 'f' then c.toNat - 'a'.toNat + 10
  else if 'A' ≤ c && c ≤ 'F' then c.toNat - 'A'.toNat + 10
  else 0

def isLetterLike (c : Char) : Bool :=
  ('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z') ||
  -- Common mathematical / Greek / subscript / double-struck Unicode ranges used in Lean identifiers
  (0x03B1 ≤ c.toNat && c.toNat ≤ 0x03C9 && c.toNat != 0x03BB) || -- α..ω except λ
  (0x0391 ≤ c.toNat && c.toNat ≤ 0x03A9 && c.toNat != 0x03A0 && c.toNat != 0x03A3) ||
  (0x2070 ≤ c.toNat && c.toNat ≤ 0x209F) || -- superscripts/subscripts ₀..₉
  (0x2100 ≤ c.toNat && c.toNat ≤ 0x214F)    -- double-struck letters ℕ, ℤ, ℚ, ℝ, ℂ

def isIdFirst (c : Char) : Bool :=
  isLetterLike c || c == '_'

def isIdRest (c : Char) : Bool :=
  isLetterLike c || isDigitChar c || c == '_' || c == '\'' || c == '?' || c == '!'

/-- Skip to the end of a `--` line comment on a `List Char` tail in $O(1)$ per character. -/
def skipLineCommentChars : List Char → Nat → Bool → (List Char × Nat × Bool)
  | [], pos, seenNl          => ([], pos, seenNl)
  | '\n' :: cs, pos, _       => (cs, pos + 1, true)
  | _ :: cs, pos, seenNl     => skipLineCommentChars cs (pos + 1) seenNl

def skipLineComment (c : InputContext) (pos : Nat) : Nat :=
  (skipLineCommentChars (c.charsFrom pos) pos false).2.1

/-- Skip a nested `/- ... -/` block comment on a `List Char` tail in $O(1)$ per character. -/
def skipBlockCommentChars : List Char → Nat → Nat → Bool → Option (List Char × Nat × Bool)
  | [], _, _, _ => none
  | '/' :: '-' :: cs, pos, nesting, seenNl =>
    skipBlockCommentChars cs (pos + 2) (nesting + 1) seenNl
  | '-' :: '/' :: cs, pos, nesting, seenNl =>
    if nesting <= 1 then some (cs, pos + 2, seenNl)
    else skipBlockCommentChars cs (pos + 2) (nesting - 1) seenNl
  | ch :: cs, pos, nesting, seenNl =>
    skipBlockCommentChars cs (pos + 1) nesting (seenNl || ch == '\n')

def skipBlockComment (c : InputContext) (pos : Nat) : Option Nat :=
  (skipBlockCommentChars (c.charsFrom pos) pos 1 false).map (·.2.1)

/-- Advance past whitespace, `--` line comments, and `/- ... -/` block comments on a `List Char` tail,
    returning `(remainingChars, nextPos, hasLeadingNewline)` in a single $O(1)$-per-char pass! -/
def skipWhitespaceChars (maxPos : Nat) : Nat → List Char → Nat → Bool → (List Char × Nat × Bool)
  | 0, cs, pos, seenNl => (cs, pos, seenNl)
  | fuel + 1, cs, pos, seenNl =>
    match cs with
    | [] => ([], pos, seenNl)
    | '-' :: '-' :: rest =>
      let (cs', pos', seenNl') := skipLineCommentChars rest (pos + 2) seenNl
      skipWhitespaceChars maxPos fuel cs' pos' seenNl'
    | '/' :: '-' :: rest =>
      match skipBlockCommentChars rest (pos + 2) 1 seenNl with
      | some (cs', pos', seenNl') => skipWhitespaceChars maxPos fuel cs' pos' seenNl'
      | none                      => ([], maxPos, seenNl)
    | ch :: rest =>
      if isSpaceChar ch then
        skipWhitespaceChars maxPos fuel rest (pos + 1) (seenNl || ch == '\n')
      else
        (cs, pos, seenNl)

/-- Return the character index after skipping whitespace and comments starting at `pos`. -/
def skipWhitespace (c : InputContext) (pos : Nat) : Nat :=
  let tail := c.charsFrom pos
  (skipWhitespaceChars c.size (c.size - pos + 1) tail pos false).2.1

/-- Advance past horizontal spaces (`' '` and `'\t'`) on a `List Char` tail in $O(1)$ per char. -/
def skipHorizontalWhitespaceChars : List Char → Nat → Nat
  | ' '  :: cs, pos => skipHorizontalWhitespaceChars cs (pos + 1)
  | '\t' :: cs, pos => skipHorizontalWhitespaceChars cs (pos + 1)
  | _, pos          => pos

def skipHorizontalWhitespace (c : InputContext) (pos : Nat) : Nat :=
  skipHorizontalWhitespaceChars (c.charsFrom pos) pos

/-- Check if a character list contains a newline (`'\n'`) within `limit` characters. -/
def charsContainNewline : List Char → Nat → Bool
  | _, 0          => false
  | [], _         => false
  | '\n' :: _, _  => true
  | _ :: cs, k + 1 => charsContainNewline cs k

/-- Check if a token's leading trivia contains a newline (`'\n'`).
    Reads the compact leading marker stored by `mkOriginalSourceInfoWithNl` in $O(1)$
    (without calling `.toUTF8` on the full source string!). -/
def hasLeadingNewline (stx : Ix.Syntax) : Bool :=
  match Syntax.getHeadInfo? 8 stx with
  | some (.original leading _ _ _) =>
    !Nat.beq leading.stopPos leading.startPos &&
    charsContainNewline leading.str.toList (leading.stopPos - leading.startPos)
  | _ => false

/-- Construct an `Ix.SourceInfo.original` given the precomputed `hasNl : Bool` from `skipWhitespaceChars`
    in $O(1)$ time and space (retaining no reference to the full source buffer `c.input`). -/
def mkOriginalSourceInfoFast (hasNl : Bool) (tokStart tokStop : Nat) : Ix.SourceInfo :=
  let leading : Ix.Substring :=
    if hasNl then { str := "\n", startPos := 0, stopPos := 1 }
    else { str := "", startPos := 0, stopPos := 0 }
  let trailing : Ix.Substring := { str := "", startPos := 0, stopPos := 0 }
  .original leading tokStart trailing tokStop

/-- Construct an `Ix.SourceInfo.original` for a token spanning `[tokStart, tokStop)`
    with leading trivia `[leadStart, tokStart)` and trailing trivia `[tokStop, trailStop)`. -/
def mkOriginalSourceInfo (c : InputContext) (leadStart tokStart tokStop _trailStop : Nat) :
    Ix.SourceInfo :=
  let hasNl := charsContainNewline (c.charsFrom leadStart) (tokStart - leadStart)
  mkOriginalSourceInfoFast hasNl tokStart tokStop

/-! ## Token Scanners (Numbers, Strings, Chars, Hash Refs, Identifiers, Operators) -/

/-- Scan digits matching `pred` (plus `_`) on a `List Char` tail in $O(1)$ per char,
    accumulating the matched characters in reverse in `revAcc`. -/
def scanDigitsChars (pred : Char → Bool) : List Char → Nat → List Char → (List Char × List Char × Nat)
  | [], pos, revAcc => ([], revAcc, pos)
  | ch :: cs, pos, revAcc =>
    if pred ch || ch == '_' then
      scanDigitsChars pred cs (pos + 1) (ch :: revAcc)
    else
      (ch :: cs, revAcc, pos)

/-- Scan a base-10, hex (`0x`), or binary (`0b`) natural number literal on `List Char`. -/
def scanNumberChars : List Char → Nat → (String × List Char × Nat)
  | '0' :: 'x' :: cs, pos =>
    let (rem, revHex, endPos) := scanDigitsChars isHexDigitChar cs (pos + 2) ['x', '0']
    (String.ofList revHex.reverse, rem, endPos)
  | '0' :: 'X' :: cs, pos =>
    let (rem, revHex, endPos) := scanDigitsChars isHexDigitChar cs (pos + 2) ['X', '0']
    (String.ofList revHex.reverse, rem, endPos)
  | '0' :: 'b' :: cs, pos =>
    let (rem, revBin, endPos) := scanDigitsChars (fun ch => ch == '0' || ch == '1') cs (pos + 2) ['b', '0']
    (String.ofList revBin.reverse, rem, endPos)
  | '0' :: 'B' :: cs, pos =>
    let (rem, revBin, endPos) := scanDigitsChars (fun ch => ch == '0' || ch == '1') cs (pos + 2) ['B', '0']
    (String.ofList revBin.reverse, rem, endPos)
  | cs, pos =>
    let (rem, revDec, endPos) := scanDigitsChars isDigitChar cs pos []
    (String.ofList revDec.reverse, rem, endPos)

def scanNumberEnd (c : InputContext) (pos : Nat) : Nat :=
  (scanNumberChars (c.charsFrom pos) pos).2.2

/-- Parse the numeric value of a scanned number literal string. -/
def parseNatLiteral (raw : String) : Option Nat :=
  let cs := raw.toList.filter (· != '_')
  match cs with
  | '0' :: 'x' :: hex | '0' :: 'X' :: hex =>
    if hex.isEmpty || !hex.all isHexDigitChar then none
    else some (hex.foldl (fun acc d => acc * 16 + hexDigitVal d) 0)
  | '0' :: 'b' :: bin | '0' :: 'B' :: bin =>
    if bin.isEmpty || !bin.all (fun ch => ch == '0' || ch == '1') then none
    else some (bin.foldl (fun acc d => acc * 2 + (if d == '1' then 1 else 0)) 0)
  | dec =>
    if dec.isEmpty || !dec.all isDigitChar then none
    else some (dec.foldl (fun acc d => acc * 10 + (d.toNat - '0'.toNat)) 0)

/-- Scan a string literal starting after the opening `"` on a `List Char` tail.
    Returns `some (decodedString, remainingChars, posAfterClosingQuote)` or `none`. -/
def scanStringLitChars : List Char → Nat → List Char → Option (String × List Char × Nat)
  | [], _, _                  => none
  | '"' :: cs, pos, acc       => some (String.ofList acc.reverse, cs, pos + 1)
  | '\n' :: _, _, _           => none
  | '\\' :: esc :: cs, pos, acc =>
    match esc with
    | 'n'  => scanStringLitChars cs (pos + 2) ('\n' :: acc)
    | 't'  => scanStringLitChars cs (pos + 2) ('\t' :: acc)
    | 'r'  => scanStringLitChars cs (pos + 2) ('\r' :: acc)
    | '\\' => scanStringLitChars cs (pos + 2) ('\\' :: acc)
    | '"'  => scanStringLitChars cs (pos + 2) ('"'  :: acc)
    | '\'' => scanStringLitChars cs (pos + 2) ('\'' :: acc)
    | '0'  => scanStringLitChars cs (pos + 2) ('\x00' :: acc)
    | 'x'  =>
      match cs with
      | d1 :: d2 :: rest =>
        if isHexDigitChar d1 && isHexDigitChar d2 then
          let ch := Char.ofNat (hexDigitVal d1 * 16 + hexDigitVal d2)
          scanStringLitChars rest (pos + 4) (ch :: acc)
        else none
      | _ => none
    | other => scanStringLitChars cs (pos + 2) (other :: acc)
  | ['\\'], _, _              => none
  | ch :: cs, pos, acc        => scanStringLitChars cs (pos + 1) (ch :: acc)

def scanStringLit (c : InputContext) (posAfterOpenQuote : Nat) : Option (String × Nat) :=
  match scanStringLitChars (c.charsFrom posAfterOpenQuote) posAfterOpenQuote [] with
  | some (s, _, nextPos) => some (s, nextPos)
  | none                 => none

/-- Scan a character literal starting after the opening `'` on a `List Char` tail. -/
def scanCharLitChars : List Char → Nat → Option (Char × List Char × Nat)
  | '\\' :: esc :: '\'' :: cs, pos =>
    let decoded := match esc with
      | 'n'  => '\n'
      | 't'  => '\t'
      | 'r'  => '\r'
      | '\\' => '\\'
      | '\'' => '\''
      | '"'  => '"'
      | '0'  => '\x00'
      | ch   => ch
    some (decoded, cs, pos + 3)
  | ch :: '\'' :: cs, pos =>
    if ch != '\'' && ch != '\\' then some (ch, cs, pos + 2)
    else none
  | _, _ => none

def scanCharLit (c : InputContext) (posAfterOpenQuote : Nat) : Option (Char × Nat) :=
  match scanCharLitChars (c.charsFrom posAfterOpenQuote) posAfterOpenQuote with
  | some (ch, _, nextPos) => some (ch, nextPos)
  | none                  => none

/-- Scan `[isIdRest]*` on a `List Char` tail in $O(1)$ per char. -/
def scanIdentRestChars : List Char → Nat → List Char → (List Char × List Char × Nat)
  | [], pos, revAcc => ([], revAcc.reverse, pos)
  | ch :: cs, pos, revAcc =>
    if isIdRest ch then
      scanIdentRestChars cs (pos + 1) (ch :: revAcc)
    else
      (ch :: cs, revAcc.reverse, pos)

/-- Scan an escaped identifier component `«...»` starting after `«` on a `List Char` tail. -/
def scanEscapedIdentChars : List Char → Nat → List Char → Option (List Char × List Char × Nat)
  | [], _, _ => none
  | '»' :: cs, pos, revAcc => some (cs, revAcc.reverse, pos + 1)
  | ch :: cs, pos, revAcc  => scanEscapedIdentChars cs (pos + 1) (ch :: revAcc)

/-- Scan a single identifier component on a `List Char` tail in $O(1)$ per char.
    Returns `some (partChars, partString, remainingChars, nextPos)` or `none`. -/
def scanOneIdentComponentChars : List Char → Nat → Option (List Char × String × List Char × Nat)
  | '«' :: cs, pos =>
    match scanEscapedIdentChars cs (pos + 1) [] with
    | some (rem, partCs, endPos) => some (partCs, String.ofList partCs, rem, endPos)
    | none => none
  | ch :: cs, pos =>
    if isIdFirst ch then
      let (rem, partCs, endPos) := scanIdentRestChars cs (pos + 1) [ch]
      some (partCs, String.ofList partCs, rem, endPos)
    else
      none
  | [], _ => none

/-- Scan a single identifier component (either `«...»` or `isIdFirst...`).
    Returns `some (componentString, nextPos)` or `none`. -/
def scanOneIdentComponent (c : InputContext) (pos : Nat) : Option (String × Nat) :=
  match scanOneIdentComponentChars (c.charsFrom pos) pos with
  | some (_, partStr, _, endPos) => some (partStr, endPos)
  | none                         => none

/-- Scan dotted identifier components `A.B.c` on a `List Char` tail in $O(1)$ per char. -/
def scanHierarchicalIdentCharsAux : Nat → List Char → Nat → Ix.Name → (Ix.Name × List Char × Nat)
  | 0, cs, pos, acc => (acc, cs, pos)
  | fuel + 1, '.' :: cs, pos, acc =>
    match scanOneIdentComponentChars cs (pos + 1) with
    | some (_, partStr, rem, nextPos) =>
      scanHierarchicalIdentCharsAux fuel rem nextPos (Name.mkStr acc partStr)
    | none =>
      (acc, '.' :: cs, pos)
  | _, cs, pos, acc => (acc, cs, pos)

def scanHierarchicalIdentChars (cs : List Char) (pos : Nat) :
    Option (Ix.Name × List Char × String × List Char × Nat × Bool) :=
  match scanOneIdentComponentChars cs pos with
  | none => none
  | some (firstCs, firstPart, rem1, pos1) =>
    let firstName := Name.mkStr Name.mkAnon firstPart
    let (fullName, remEnd, endPos) := scanHierarchicalIdentCharsAux 64 rem1 pos1 firstName
    some (fullName, firstCs, firstPart, remEnd, endPos, Nat.beq endPos pos1)

/-- Check if `cs : List Char` is a reserved keyword in `env.keywords`. -/
def isKeywordChars (env : IxParserEnv) (cs : List Char) : Bool :=
  env.keywords.findExact? cs == some true

/-- Check if `s` is a reserved keyword in `env.keywords`. -/
def isKeyword (env : IxParserEnv) (s : String) : Bool :=
  isKeywordChars env s.toList

/-- Construct the updated `ParserState` after scanning a token `tok` spanning `[leadStart, trailStop)`,
    strictly forcing `newLen`, `leadStart`, and `trailStop` without `{ s with ... }` projections. -/
def mkScannedState (s : ParserState) (leadStart trailStop : Nat) (tok : Ix.Syntax) : ParserState :=
  match s with
  | ⟨⟨rev, len⟩, lhsPrec, _, _, _⟩ =>
    let newLen := len + 1
    let stack' : SyntaxStack :=
      if Nat.beq newLen 0 then ⟨tok :: rev, 0⟩ else ⟨tok :: rev, newLen⟩
    let cache' : TokenCacheEntry :=
      if Nat.beq leadStart 0 && Nat.beq trailStop 0 then ⟨0, 0, tok⟩
      else ⟨leadStart, trailStop, tok⟩
    if Nat.beq trailStop 0 then
      ⟨stack', lhsPrec, 0, cache', none⟩
    else
      ⟨stack', lhsPrec, trailStop, cache', none⟩

/-- Core token scanner: reads one token starting at `s.pos` with a SINGLE $O(\log N)$
    `c.charsFrom` lookup, scanning leading whitespace, the token body, and trailing
    horizontal whitespace in $O(1)$ per character on `List Char`! -/
def scanNextToken (ctx : IxParserContext) (s : ParserState) : ParserState :=
  let c := ctx.inputCtx
  let leadStart := s.pos
  let leadChars := c.charsFrom leadStart
  let (tokChars, tokStart, hasNl) := skipWhitespaceChars c.size (c.size - leadStart + 1) leadChars leadStart false
  match tokChars with
  | [] =>
    s.setPos tokStart |>.mkEOIError
  | ch :: restTokChars =>
    -- 1. Content-hash reference `#<hex-digits>`
    let isHashHex := ch == '#' && match restTokChars with | d :: _ => isHexDigitChar d | [] => false
    if isHashHex then
      let (afterHex, revHex, hexEnd) := scanDigitsChars isHexDigitChar restTokChars (tokStart + 1) []
      let trailStop := skipHorizontalWhitespaceChars afterHex hexEnd
      let info := mkOriginalSourceInfoFast hasNl tokStart hexEnd
      let hexVal := String.ofList revHex.reverse
      let tok := Syntax.mkNode SyntaxKind.hashRef #[Syntax.mkAtom info hexVal] info
      mkScannedState s leadStart trailStop tok
    -- 2. String literal `"..."`
    else if ch == '"' then
      match scanStringLitChars restTokChars (tokStart + 1) [] with
      | some (decoded, afterStr, tokStop) =>
        let trailStop := skipHorizontalWhitespaceChars afterStr tokStop
        let info := mkOriginalSourceInfoFast hasNl tokStart tokStop
        let tok := Syntax.mkNode SyntaxKind.strLit #[Syntax.mkAtom info decoded] info
        mkScannedState s leadStart trailStop tok
      | none =>
        s.setPos tokStart |>.mkUnexpectedError "unterminated string literal"
    -- 3. Character literal `'c'` (only when not a prime inside an identifier)
    else if ch == '\'' && (scanCharLitChars restTokChars (tokStart + 1)).isSome then
      match scanCharLitChars restTokChars (tokStart + 1) with
      | some (decodedChar, afterChar, tokStop) =>
        let trailStop := skipHorizontalWhitespaceChars afterChar tokStop
        let info := mkOriginalSourceInfoFast hasNl tokStart tokStop
        let tok := Syntax.mkNode SyntaxKind.charLit
          #[Syntax.mkAtom info (String.singleton decodedChar)] info
        mkScannedState s leadStart trailStop tok
      | none =>
        s.setPos tokStart |>.mkUnexpectedError "invalid character literal"
    -- 4. Numeric literal `0..9`
    else if isDigitChar ch then
      let (rawNum, afterNum, tokStop) := scanNumberChars tokChars tokStart
      match parseNatLiteral rawNum with
      | some n =>
        let trailStop := skipHorizontalWhitespaceChars afterNum tokStop
        let info := mkOriginalSourceInfoFast hasNl tokStart tokStop
        let tok := Syntax.mkNode SyntaxKind.numLit #[Syntax.mkAtom info (toString n)] info
        mkScannedState s leadStart trailStop tok
      | none =>
        s.setPos tokStart |>.mkUnexpectedError s!"invalid numeric literal '{rawNum}'"
    -- 5. Identifier or keyword
    else if isIdFirst ch || ch == '«' then
      match scanHierarchicalIdentChars tokChars tokStart with
      | some (name, firstCs, firstPart, afterIdent, tokStop, isSinglePart) =>
        let trailStop := skipHorizontalWhitespaceChars afterIdent tokStop
        let info := mkOriginalSourceInfoFast hasNl tokStart tokStop
        -- If it is a single unescaped component that matches a reserved keyword, emit an `.atom`
        let isSingleUnescaped := ch != '«' && isSinglePart
        let tok :=
          if isSingleUnescaped && isKeywordChars ctx.env firstCs then
            Syntax.mkAtom info firstPart
          else
            let rawSub : Ix.Substring := { str := firstPart, startPos := 0, stopPos := firstPart.utf8ByteSize }
            Syntax.mkIdent info rawSub name
        mkScannedState s leadStart trailStop tok
      | none =>
        s.setPos tokStart |>.mkUnexpectedError "invalid identifier"
    -- 6. Operator / punctuation symbol from `ctx.env.tokens`
    else
      match Trie.matchPrefixList tokStart none tokChars ctx.env.tokens with
      | some (sym, tokStop) =>
        let symLen := tokStop - tokStart
        let afterSym := tokChars.drop symLen
        let trailStop := skipHorizontalWhitespaceChars afterSym tokStop
        let info := mkOriginalSourceInfoFast hasNl tokStart tokStop
        let tok := Syntax.mkAtom info sym
        mkScannedState s leadStart trailStop tok
      | none =>
        s.setPos tokStart |>.mkUnexpectedError s!"unexpected character '{ch}'"

/-- Read one token using the single-token cache when `s.cache.startPos == s.pos`. -/
def tokenFn (ctx : IxParserContext) (s : ParserState) : ParserState :=
  s.bindState fun s =>
    match s with
    | ⟨stack, lhsPrec, pos, cache, err⟩ =>
      if Nat.beq cache.startPos pos then
        match stack.push cache.token with
        | ⟨rev', len'⟩ =>
          if Nat.beq cache.stopPos 0 then ⟨⟨rev', len'⟩, lhsPrec, 0, cache, err⟩
          else ⟨⟨rev', len'⟩, lhsPrec, cache.stopPos, cache, err⟩
      else
        scanNextToken ctx s

/-- Peek at the next token without consuming it, passing `(Option Syntax, updatedCacheState)`
    directly to continuation `k` with zero `Prod` allocation and zero stack push/shrink on cache hit. -/
def bindPeek (ctx : IxParserContext) (s : ParserState)
    (k : Option Ix.Syntax → ParserState → α) : α :=
  s.bindState fun s =>
    match s with
    | ⟨stack, lhsPrec, iniPos, cache, err⟩ =>
      if err.isNone && Nat.beq cache.startPos iniPos then
        k (some cache.token) s
      else
        (scanNextToken ctx s).bindState fun s' =>
          if s'.hasError then
            k none ⟨stack, lhsPrec, iniPos, s'.cache, none⟩
          else
            k (some s'.cache.token) ⟨stack, lhsPrec, iniPos, s'.cache, none⟩

/-- Peek at the next token without consuming it (returns `(Option Syntax, updatedCacheState)`). -/
def peekToken (ctx : IxParserContext) (s : ParserState) : Option Ix.Syntax × ParserState :=
  bindPeek ctx s fun tok? s' => (tok?, s')

/-- Check if the input is at EOI (after skipping whitespace and comments). -/
def atEOI (ctx : IxParserContext) (s : ParserState) : Bool :=
  s.bindState fun s =>
    let pos' := skipWhitespace ctx.inputCtx s.pos
    ctx.inputCtx.atEnd pos'

/-! ## Core Combinators -/

/-- Run `p` and wrap all syntax nodes pushed since entry into `Syntax.mkNode k`. -/
def nodeFn (k : Ix.Name) (p : ParserFn) : ParserFn := fun ctx s =>
  s.bindState fun s =>
    let iniSz := s.stackSize
    (p ctx s).bindState fun s' =>
      s'.mkNode k iniSz

/-- Run `p`; if `p` fails, reset `s.pos` and `s.stxStack` to the entry state
    (while keeping the error message). -/
def atomicFn (p : ParserFn) : ParserFn := fun ctx s =>
  s.bindState fun s =>
    let iniSz := s.stackSize
    let iniPos := s.pos
    (p ctx s).bindState fun s' =>
      if s'.hasError then
        match s' with
        | ⟨stack', lhsPrec', _, cache', err'⟩ =>
          match stack'.shrink iniSz with
          | ⟨rev', len'⟩ => ⟨⟨rev', len'⟩, lhsPrec', iniPos, cache', err'⟩
      else
        s'

/-- Ordered choice with LL(1) commitment: if `p` fails *without* advancing `pos`,
    backtrack and try `q` (merging errors if `q` also fails at the same position). -/
def orelseFn (p q : ParserFn) : ParserFn := fun ctx s =>
  s.bindState fun s =>
    let iniSz := s.stackSize
    let iniPos := s.pos
    (p ctx s).bindState fun s1 =>
      match s1.errorMsg with
      | none => s1
      | some e1 =>
        if !Nat.beq s1.pos iniPos then
          s1
        else
          (s1.restore iniSz iniPos).bindState fun sRestored =>
            (q ctx sRestored).bindState fun s2 =>
              match s2.errorMsg with
              | none => s2
              | some e2 => s2.setError (ParserError.merge e1 e2)

/-- Try `p`, always backtracking on any error and trying `q`. -/
def tryOrElseFn (p q : ParserFn) : ParserFn :=
  orelseFn (atomicFn p) q

/-- Sequence two parser functions. -/
def seqFn (p q : ParserFn) : ParserFn := fun ctx s =>
  (p ctx s).bindState fun s' =>
    if s'.hasError then s' else q ctx s'

/-- Optional combinator: wraps 0 or 1 result in a `null` node (`SyntaxKind.nullKind`). -/
def optionalFn (p : ParserFn) : ParserFn := fun ctx s =>
  s.bindState fun s =>
    let iniSz := s.stackSize
    let iniPos := s.pos
    (p ctx s).bindState fun s' =>
      if s'.hasError && Nat.beq s'.pos iniPos then
        (s'.restore iniSz iniPos).mkNode SyntaxKind.nullKind iniSz
      else
        s'.mkNode SyntaxKind.nullKind iniSz

/-- Zero-or-more repetition (bounded by `fuel` and strictly advancing `pos`), wrapped in `null`. -/
def manyLoop (p : ParserFn) (ctx : IxParserContext) (s : ParserState) : Nat → ParserState
  | 0 => s
  | fuel + 1 =>
    s.bindState fun s =>
      let iniSz := s.stackSize
      let iniPos := s.pos
      (p ctx s).bindState fun s' =>
        if s'.hasError then
          if Nat.beq s'.pos iniPos then s'.restore iniSz iniPos else s'
        else if Nat.beq s'.pos iniPos then
          s'
        else
          manyLoop p ctx s' fuel

def manyFn (p : ParserFn) : ParserFn := fun ctx s =>
  s.bindState fun s =>
    let iniSz := s.stackSize
    let fuel := ctx.inputCtx.size - s.pos + 1
    (manyLoop p ctx s fuel).bindState fun s' =>
      s'.mkNode SyntaxKind.nullKind iniSz

/-- One-or-more repetition wrapped in `null`. -/
def many1Fn (p : ParserFn) : ParserFn := fun ctx s =>
  s.bindState fun s =>
    let iniSz := s.stackSize
    (p ctx s).bindState fun s1 =>
      if s1.hasError then
        s1.mkNode SyntaxKind.nullKind iniSz
      else
        let fuel := ctx.inputCtx.size - s1.pos + 1
        (manyLoop p ctx s1 fuel).bindState fun s2 =>
          s2.mkNode SyntaxKind.nullKind iniSz

/-- Separated list `p (sep p)*` wrapped in `null`. -/
def sepByLoop (p sep : ParserFn) (allowTrailing : Bool) (ctx : IxParserContext) (s : ParserState) :
    Nat → ParserState
  | 0 => s
  | fuel + 1 =>
    s.bindState fun s =>
      let sepIniSz := s.stackSize
      let sepIniPos := s.pos
      (sep ctx s).bindState fun sSep =>
        if sSep.hasError then
          if Nat.beq sSep.pos sepIniPos then sSep.restore sepIniSz sepIniPos else sSep
        else
          (sSep.shrinkStack sepIniSz).bindState fun sAfterSep =>
            let pIniSz := sAfterSep.stackSize
            let pIniPos := sAfterSep.pos
            (p ctx sAfterSep).bindState fun sElem =>
              if sElem.hasError then
                if allowTrailing && Nat.beq sElem.pos pIniPos then
                  sElem.restore pIniSz pIniPos
                else
                  sElem
              else
                sepByLoop p sep allowTrailing ctx sElem fuel

def sepBy1Fn (p sep : ParserFn) (allowTrailing : Bool := false) : ParserFn := fun ctx s =>
  s.bindState fun s =>
    let iniSz := s.stackSize
    (p ctx s).bindState fun s1 =>
      if s1.hasError then
        s1.mkNode SyntaxKind.nullKind iniSz
      else
        let fuel := ctx.inputCtx.size - s1.pos + 1
        (sepByLoop p sep allowTrailing ctx s1 fuel).bindState fun s2 =>
          s2.mkNode SyntaxKind.nullKind iniSz

def sepByFn (p sep : ParserFn) (allowTrailing : Bool := false) : ParserFn := fun ctx s =>
  s.bindState fun s =>
    let iniSz := s.stackSize
    let iniPos := s.pos
    (p ctx s).bindState fun s1 =>
      if s1.hasError then
        if Nat.beq s1.pos iniPos then
          (s1.restore iniSz iniPos).mkNode SyntaxKind.nullKind iniSz
        else
          s1.mkNode SyntaxKind.nullKind iniSz
      else
        let fuel := ctx.inputCtx.size - s1.pos + 1
        (sepByLoop p sep allowTrailing ctx s1 fuel).bindState fun s2 =>
          s2.mkNode SyntaxKind.nullKind iniSz

/-! ## Primitive Token Parsers -/

/-- Expect a specific `.atom` symbol `sym`. -/
def symbolFn (sym : String) : ParserFn := fun ctx s =>
  s.bindState fun s =>
    let iniSz := s.stackSize
    let iniPos := s.pos
    (tokenFn ctx s).bindState fun s' =>
      if s'.hasError then
        s'.mkErrorAt sym iniPos iniSz
      else
        match s'.stxStack.back with
        | .atom _ v =>
          if v == sym then s'
          else s'.mkErrorAt sym iniPos iniSz
        | _ => s'.mkErrorAt sym iniPos iniSz

/-- Expect a specific non-reserved identifier word (e.g., soft keyword like `borrow`). -/
def nonReservedSymbolFn (sym : String) : ParserFn := fun ctx s =>
  s.bindState fun s =>
    let iniSz := s.stackSize
    let iniPos := s.pos
    (tokenFn ctx s).bindState fun s' =>
      if s'.hasError then
        s'.mkErrorAt sym iniPos iniSz
      else
        match s'.stxStack.back with
        | .ident info _ (.str (.anonymous _) v _) _ =>
          if v == sym then
            let s' := s'.popSyntax
            s'.pushSyntax (.atom info sym)
          else
            s'.mkErrorAt sym iniPos iniSz
        | .atom _ v =>
          if v == sym then s'
          else s'.mkErrorAt sym iniPos iniSz
        | _ => s'.mkErrorAt sym iniPos iniSz

/-- Expect an identifier token (`.ident`). -/
def identFn : ParserFn := fun ctx s =>
  s.bindState fun s =>
    let iniSz := s.stackSize
    let iniPos := s.pos
    (tokenFn ctx s).bindState fun s' =>
      if s'.hasError then
        s'.mkErrorAt "identifier" iniPos iniSz
      else
        match s'.stxStack.back with
        | .ident .. => s'
        | _         => s'.mkErrorAt "identifier" iniPos iniSz

/-- Expect a numeric literal token (`SyntaxKind.numLit`). -/
def numLitFn : ParserFn := fun ctx s =>
  s.bindState fun s =>
    let iniSz := s.stackSize
    let iniPos := s.pos
    (tokenFn ctx s).bindState fun s' =>
      if s'.hasError then
        s'.mkErrorAt "numeric literal" iniPos iniSz
      else if Syntax.isOfKind s'.stxStack.back SyntaxKind.numLit then
        s'
      else
        s'.mkErrorAt "numeric literal" iniPos iniSz

/-- Expect a string literal token (`SyntaxKind.strLit`). -/
def strLitFn : ParserFn := fun ctx s =>
  s.bindState fun s =>
    let iniSz := s.stackSize
    let iniPos := s.pos
    (tokenFn ctx s).bindState fun s' =>
      if s'.hasError then
        s'.mkErrorAt "string literal" iniPos iniSz
      else if Syntax.isOfKind s'.stxStack.back SyntaxKind.strLit then
        s'
      else
        s'.mkErrorAt "string literal" iniPos iniSz

/-- Expect a character literal token (`SyntaxKind.charLit`). -/
def charLitFn : ParserFn := fun ctx s =>
  s.bindState fun s =>
    let iniSz := s.stackSize
    let iniPos := s.pos
    (tokenFn ctx s).bindState fun s' =>
      if s'.hasError then
        s'.mkErrorAt "character literal" iniPos iniSz
      else if Syntax.isOfKind s'.stxStack.back SyntaxKind.charLit then
        s'
      else
        s'.mkErrorAt "character literal" iniPos iniSz

/-- Expect a content-hash reference token (`#<hex-digits>`, `SyntaxKind.hashRef`). -/
def hashRefFn : ParserFn := fun ctx s =>
  s.bindState fun s =>
    let iniSz := s.stackSize
    let iniPos := s.pos
    (tokenFn ctx s).bindState fun s' =>
      if s'.hasError then
        s'.mkErrorAt "content-hash reference (#<hex>)" iniPos iniSz
      else if Syntax.isOfKind s'.stxStack.back SyntaxKind.hashRef then
        s'
      else
        s'.mkErrorAt "content-hash reference (#<hex>)" iniPos iniSz

/-- Run `p` with a modified minimum precedence `prec`. -/
def withPrecFn (prec : Nat) (p : ParserFn) : ParserFn := fun ctx s =>
  match ctx with
  | ⟨inputCtx, env, _⟩ =>
    if Nat.beq prec 0 then p ⟨inputCtx, env, 0⟩ s
    else p ⟨inputCtx, env, prec⟩ s

end Ix.Frontend.Parser
