/-
  Ix.Frontend.Parser.Types: Pure, total parser state, syntax stack, error model,
  and character-indexed input context for the Ix Frontend.
-/
module

public import Ix.Frontend.Syntax
public import Ix.Frontend.Parser.Trie

@[expose] public section

namespace Ix.Frontend.Parser

/-! ## Character-Indexed `InputContext` -/

/-- Balanced binary segment tree over character suffixes `(ch, tailChars)`,
    providing $O(\log N)$ random access by character index without `Array`/`Fin` proof terms. -/
inductive CharSegTree where
  | empty : CharSegTree
  | leaf  : Char → List Char → CharSegTree
  | node  : Nat → CharSegTree → CharSegTree → CharSegTree
  deriving Repr, Inhabited

/-- Pure input context that pre-decodes `input` into a spine of characters `chars`,
    `charCount`, and an $O(\log N)$ `CharSegTree`. -/
structure InputContext where
  fileName  : String
  input     : String
  chars     : List Char
  charCount : Nat
  tree      : CharSegTree := .empty
  deriving Repr, Inhabited

namespace InputContext

/-- Force `n : Nat` to WHNF in the kernel via `Nat.casesOn` (`0` or `m + 1`) so `m` is bound
    to the reduced `KLiteral.Nat (n - 1)` and `n` never accumulates unreduced arithmetic or
    scanner thunks across recursive calls under call-by-name reduction. -/
@[inline] def bindNat (n : Nat) (k : Nat → α) : α :=
  match n with
  | 0     => k 0
  | m + 1 => k (Nat.succ m)

/-- Build a balanced binary tree over `count` suffixes of `cs` in $O(N)$ steps,
    structurally recursive on `depth : Nat` (compiled directly to `Nat.rec`),
    forcing `leftLen`, `rightLen`, `leftTree`, and `rightTree` before constructing `.node`. -/
def buildCharSegTreeAux : Nat → Nat → List Char → (CharSegTree × List Char)
  | 0, _, cs => (.empty, cs)
  | depth + 1, count, cs =>
    if Nat.beq count 0 then
      (.empty, cs)
    else if Nat.beq count 1 then
      match cs with
      | c :: cs' => (.leaf c (c :: cs'), cs')
      | []       => (.empty, [])
    else
      bindNat (count / 2) fun leftLen =>
      bindNat (count - leftLen) fun rightLen =>
      match buildCharSegTreeAux depth leftLen cs with
      | (leftTree, cs1) =>
        match buildCharSegTreeAux depth rightLen cs1 with
        | (rightTree, cs2) =>
          match leftTree, rightTree with
          | lt, rt => (.node leftLen lt rt, cs2)

/-- Look up character index `idx` in `CharSegTree` in $O(\log N)$ steps. -/
def lookupSegTree : CharSegTree → Nat → Option (Char × List Char)
  | .empty, _ => none
  | .leaf c tail, 0 => some (c, tail)
  | .leaf _ _, _ => none
  | .node leftLen left right, idx =>
    if Nat.ble (idx + 1) leftLen then
      lookupSegTree left idx
    else
      lookupSegTree right (idx - leftLen)

/-- Strictly count characters in `List Char` in $O(N)$ tail-recursive steps. -/
def countChars : List Char → Nat → Nat
  | [], cnt => cnt
  | _ :: cs, cnt =>
    bindNat (cnt + 1) fun cnt' => countChars cs cnt'

/-- Construct an `InputContext` from a source string and optional file name. -/
def mkInputContext (input : String) (fileName : String := "<input>") : InputContext :=
  match input.toList with
  | [] => { fileName, input, chars := [], charCount := 0, tree := .empty }
  | c0 :: cs0 =>
    let chars := c0 :: cs0
    bindNat (countChars chars 0) fun charCount =>
      match buildCharSegTreeAux 20 charCount chars with
      | (tree, _) =>
        match tree with
        | .empty      => { fileName, input, chars, charCount, tree := .empty }
        | .leaf c tl  => { fileName, input, chars, charCount, tree := .leaf c tl }
        | .node n l r => { fileName, input, chars, charCount, tree := .node n l r }

/-- Strictly destructure an `InputContext` once so its `charCount` and `CharSegTree`
    are never re-evaluated across token scans under call-by-name reduction. -/
@[inline] def bindInputCtx (c : InputContext) (k : InputContext → α) : α :=
  match c with
  | ⟨fileName, input, chars, charCount, tree⟩ =>
    bindNat charCount fun charCount' =>
      match tree with
      | .empty      => k ⟨fileName, input, chars, charCount', .empty⟩
      | .leaf ch tl => k ⟨fileName, input, chars, charCount', .leaf ch tl⟩
      | .node n l r => k ⟨fileName, input, chars, charCount', .node n l r⟩

/-- Total number of Unicode scalar characters in the input. -/
def size (c : InputContext) : Nat :=
  c.charCount

/-- True when character index `idx` is at or past the end of input. -/
def atEnd (c : InputContext) (idx : Nat) : Bool :=
  Nat.ble c.charCount idx

/-- Return the character suffix `c.chars.drop idx` in $O(\log N)$ steps via `c.tree`. -/
def charsFrom (c : InputContext) (idx : Nat) : List Char :=
  match lookupSegTree c.tree idx with
  | some (_, tail) => tail
  | none           => []

/-- Return the character at character index `idx`, if in bounds, in $O(\log N)$ steps. -/
def get? (c : InputContext) (idx : Nat) : Option Char :=
  match lookupSegTree c.tree idx with
  | some (ch, _) => some ch
  | none         => none

/-- Return the character at character index `idx`, or `default` if out of bounds, in $O(\log N)$ steps. -/
def getD (c : InputContext) (idx : Nat) (default : Char := '\x00') : Char :=
  match lookupSegTree c.tree idx with
  | some (ch, _) => ch
  | none         => default

/-- Take at most `n` elements from a `List` via `Nat` structural recursion. -/
def takeChars : Nat → List Char → List Char
  | 0, _            => []
  | _, []           => []
  | k + 1, x :: xs  => x :: takeChars k xs

/-- Extract the `String` spanning character indices `[startIdx, stopIdx)` in $O(\log N + \text{len})$. -/
def extract (c : InputContext) (startIdx stopIdx : Nat) : String :=
  String.ofList (takeChars (stopIdx - startIdx) (c.charsFrom startIdx))

/-- Compute 1-based `(line, column)` for a character index `idx` (for diagnostics). -/
def lineCol (c : InputContext) (idx : Nat) : Nat × Nat :=
  let limit := Nat.min idx c.charCount
  (c.chars.take limit).foldl (fun (line, col) ch =>
    if ch == '\n' then (line + 1, 1) else (line, col + 1)) (1, 1)

end InputContext

/-! ## `SyntaxStack` -/

/-- Pure syntax stack used by parser combinators to build `Ix.Syntax` nodes.
    Represented as a top-first list `rev` and cached `len` so `push`, `pop`, and `back`
    are $O(1)$ constructor operations with zero `Array`/`Fin` proof terms in the kernel. -/
structure SyntaxStack where
  rev : List Ix.Syntax := []
  len : Nat := 0
  deriving Repr, Inhabited, BEq

namespace SyntaxStack

def empty : SyntaxStack := { rev := [], len := 0 }

def size (s : SyntaxStack) : Nat := s.len

def isEmpty (s : SyntaxStack) : Bool := Nat.beq s.len 0

def push (s : SyntaxStack) (stx : Ix.Syntax) : SyntaxStack :=
  match s with
  | ⟨rev, len⟩ =>
    InputContext.bindNat (len + 1) fun len' => ⟨stx :: rev, len'⟩

def pop (s : SyntaxStack) : SyntaxStack :=
  match s with
  | ⟨_ :: xs, len⟩ =>
    InputContext.bindNat (len - 1) fun len' => ⟨xs, len'⟩
  | ⟨[], _⟩ => ⟨[], 0⟩

def back (s : SyntaxStack) : Ix.Syntax :=
  match s.rev with
  | x :: _ => x
  | []     => .missing

def getD (s : SyntaxStack) (i : Nat) : Ix.Syntax :=
  if Nat.ble s.len i then .missing
  else Syntax.listGetD s.rev (s.len - 1 - i) .missing

/-- Force the outer spine of `xs : List α` to WHNF before passing to `k`. -/
@[inline] def bindList (xs : List α) (k : List α → β) : β :=
  match xs with
  | []      => k []
  | y :: ys => k (y :: ys)

/-- Pop `n` elements from the top of `rev`, accumulating them in left-to-right order in `acc`. -/
def popTopN : Nat → List Ix.Syntax → List Ix.Syntax → List Ix.Syntax × List Ix.Syntax
  | 0, rev, acc           => (acc, rev)
  | _, [], acc            => (acc, [])
  | n + 1, x :: rest, acc => popTopN n rest (x :: acc)

def shrink (s : SyntaxStack) (newSize : Nat) : SyntaxStack :=
  match s with
  | ⟨rev, len⟩ =>
    if Nat.ble len newSize then ⟨rev, len⟩
    else
      InputContext.bindNat newSize fun newSize' =>
        match popTopN (len - newSize') rev [] with
        | (_, rest) =>
          bindList rest fun rest' => ⟨rest', newSize'⟩

def extract (s : SyntaxStack) (start stop : Nat) : Array Ix.Syntax :=
  let clampedStop := Nat.min stop s.len
  if Nat.ble clampedStop start then #[]
  else
    let afterStop := s.rev.drop (s.len - clampedStop)
    match popTopN (clampedStop - start) afterStop [] with
    | (items, _) =>
      bindList items fun items' => Array.mk items'

end SyntaxStack

/-! ## `ParserError` -/

/-- Deterministic parse error with character offset, unexpected message, and expected tokens. -/
structure ParserError where
  pos        : Nat := 0
  unexpected : String := ""
  expected   : List String := []
  deriving Repr, Inhabited, BEq

namespace ParserError

def merge (e1 e2 : ParserError) : ParserError :=
  if Nat.ble (e1.pos + 1) e2.pos then e2
  else if Nat.ble (e2.pos + 1) e1.pos then e1
  else
    { pos        := e1.pos
      unexpected := if e1.unexpected.isEmpty then e2.unexpected else e1.unexpected
      expected   := (e1.expected ++ e2.expected).eraseDups }

def toString (ctx : InputContext) (e : ParserError) : String :=
  let (line, col) := ctx.lineCol e.pos
  let unexp := if e.unexpected.isEmpty then "parse error" else e.unexpected
  let exp := match e.expected with
    | [] => ""
    | es => s!"; expected {strIntercalatePure ", " es}"
  s!"{ctx.fileName}:{line}:{col}: {unexp}{exp}"

end ParserError

/-! ## `TokenCacheEntry` & `ParserState` -/

/-- Single-entry token lookahead cache to avoid re-scanning tokens after backtracking. -/
structure TokenCacheEntry where
  startPos : Nat := 0xFFFFFFFF
  stopPos  : Nat := 0
  token    : Ix.Syntax := .missing
  deriving Repr, Inhabited

/-- Pure state threaded through every parser combinator. -/
structure ParserState where
  stxStack : SyntaxStack := SyntaxStack.empty
  lhsPrec  : Nat := 0
  pos      : Nat := 0
  cache    : TokenCacheEntry := {}
  errorMsg : Option ParserError := none
  deriving Repr, Inhabited

namespace ParserState

/-- Strictly destructure `s : ParserState`, forcing its stack spine, `len`, `lhsPrec`, `pos`,
    `cache`, and `errorMsg` to WHNF once so subsequent combinator steps never re-evaluate
    `s` or accumulate projection chains under call-by-name reduction. -/
def bindState (s : ParserState) (k : ParserState → α) : α :=
  match s with
  | ⟨⟨rev, len⟩, lhsPrec, pos, ⟨cStart, cStop, cTok⟩, err⟩ =>
    SyntaxStack.bindList rev fun rev' =>
    match err with
    | none   => k ⟨⟨rev', len⟩, lhsPrec, pos, ⟨cStart, cStop, cTok⟩, none⟩
    | some e => k ⟨⟨rev', len⟩, lhsPrec, pos, ⟨cStart, cStop, cTok⟩, some e⟩

def hasError (s : ParserState) : Bool :=
  s.errorMsg.isSome

def stackSize (s : ParserState) : Nat :=
  s.stxStack.size

def restore (s : ParserState) (iniSz : Nat) (iniPos : Nat) : ParserState :=
  match s with
  | ⟨stack, lhsPrec, _, cache, _⟩ =>
    match stack.shrink iniSz with
    | ⟨rev', len'⟩ =>
      InputContext.bindNat iniPos fun iniPos' =>
        ⟨⟨rev', len'⟩, lhsPrec, iniPos', cache, none⟩

def setPos (s : ParserState) (newPos : Nat) : ParserState :=
  match s with
  | ⟨stack, lhsPrec, _, cache, err⟩ =>
    InputContext.bindNat newPos fun newPos' =>
      ⟨stack, lhsPrec, newPos', cache, err⟩

def pushSyntax (s : ParserState) (stx : Ix.Syntax) : ParserState :=
  match s with
  | ⟨stack, lhsPrec, pos, cache, err⟩ =>
    match stack.push stx with
    | ⟨rev', len'⟩ => ⟨⟨rev', len'⟩, lhsPrec, pos, cache, err⟩

def popSyntax (s : ParserState) : ParserState :=
  match s with
  | ⟨stack, lhsPrec, pos, cache, err⟩ =>
    match stack.pop with
    | ⟨rev', len'⟩ => ⟨⟨rev', len'⟩, lhsPrec, pos, cache, err⟩

def shrinkStack (s : ParserState) (iniSz : Nat) : ParserState :=
  match s with
  | ⟨stack, lhsPrec, pos, cache, err⟩ =>
    match stack.shrink iniSz with
    | ⟨rev', len'⟩ => ⟨⟨rev', len'⟩, lhsPrec, pos, cache, err⟩

def mkNode (s : ParserState) (k : Ix.Name) (iniSz : Nat) : ParserState :=
  match s with
  | ⟨stack, lhsPrec, pos, cache, err⟩ =>
    if err.isSome && Nat.beq stack.len iniSz then
      match stack.push .missing with
      | ⟨rev', len'⟩ => ⟨⟨rev', len'⟩, lhsPrec, pos, cache, err⟩
    else
      let count := stack.len - iniSz
      match SyntaxStack.popTopN count stack.rev [] with
      | (children, restRev) =>
        SyntaxStack.bindList children fun children' =>
        SyntaxStack.bindList restRev fun restRev' =>
        InputContext.bindNat (iniSz + 1) fun newLen =>
          let newStack : SyntaxStack :=
            ⟨Syntax.mkNode k (Array.mk children') :: restRev', newLen⟩
          ⟨newStack, lhsPrec, pos, cache, err⟩

def mkTrailingNode (s : ParserState) (k : Ix.Name) (iniSz : Nat) (lhsPrec : Nat) : ParserState :=
  match s with
  | ⟨stack, _, pos, cache, err⟩ =>
    let baseSz := iniSz - 1
    let count := stack.len - baseSz
    match SyntaxStack.popTopN count stack.rev [] with
    | (children, restRev) =>
      SyntaxStack.bindList children fun children' =>
      SyntaxStack.bindList restRev fun restRev' =>
      InputContext.bindNat (baseSz + 1) fun newLen =>
      InputContext.bindNat lhsPrec fun lhsPrec' =>
        let newStack : SyntaxStack :=
          ⟨Syntax.mkNode k (Array.mk children') :: restRev', newLen⟩
        ⟨newStack, lhsPrec', pos, cache, err⟩

def setError (s : ParserState) (e : ParserError) : ParserState :=
  match s with
  | ⟨stack, lhsPrec, pos, cache, _⟩ => ⟨stack, lhsPrec, pos, cache, some e⟩

def mkError (s : ParserState) (expected : String) : ParserState :=
  match s with
  | ⟨stack, lhsPrec, pos, cache, _⟩ =>
    match stack.push .missing with
    | ⟨rev', len'⟩ =>
      ⟨⟨rev', len'⟩, lhsPrec, pos, cache, some { pos := pos, expected := [expected] }⟩

def mkUnexpectedError (s : ParserState) (msg : String) (expected : List String := []) : ParserState :=
  match s with
  | ⟨stack, lhsPrec, pos, cache, _⟩ =>
    ⟨stack, lhsPrec, pos, cache, some { pos := pos, unexpected := msg, expected := expected }⟩

def mkEOIError (s : ParserState) (expected : List String := []) : ParserState :=
  s.mkUnexpectedError "unexpected end of input" expected

def mkErrorAt (s : ParserState) (expected : String) (errPos : Nat) (iniSz : Nat) : ParserState :=
  match s with
  | ⟨stack, lhsPrec, _, cache, _⟩ =>
    match (stack.shrink iniSz).push .missing with
    | ⟨rev', len'⟩ =>
      InputContext.bindNat errPos fun errPos' =>
        ⟨⟨rev', len'⟩, lhsPrec, errPos', cache, some { pos := errPos', expected := [expected] }⟩

end ParserState

/-! ## `IxParserEnv` & `IxParserContext` -/

/-- User-defined or builtin operator descriptor for the Pratt expression parser. -/
inductive FixityKind where
  | infixl
  | infixr
  | infixn
  | prefixOp
  | postfixOp
  deriving BEq, DecidableEq, Repr, Inhabited

structure OperatorSpec where
  symbol   : String
  kind     : Ix.Name
  fixity   : FixityKind
  prec     : Nat
  targetFn : Option Ix.Name := none
  deriving BEq, Repr, Inhabited

/-- Pure parser environment holding token trie, reserved keywords, and operator tables. -/
structure IxParserEnv where
  tokens    : Trie String
  keywords  : Trie Bool
  operators : List OperatorSpec := []
  deriving Repr, Inhabited

namespace IxParserEnv

/-- Strictly destructure `env : IxParserEnv`, forcing its `tokens` and `keywords` tries
    and `operators` spine once so they are never re-evaluated across token scans. -/
@[inline] def bindParserEnv (env : IxParserEnv) (k : IxParserEnv → α) : α :=
  match env with
  | ⟨.node tv tch, .node kv kch, ops⟩ =>
    SyntaxStack.bindList tch fun tch' =>
    SyntaxStack.bindList kch fun kch' =>
    SyntaxStack.bindList ops fun ops' =>
      k ⟨.node tv tch', .node kv kch', ops'⟩

end IxParserEnv

/-- Reader context for `ParserFn`. -/
structure IxParserContext where
  inputCtx : InputContext
  env      : IxParserEnv
  prec     : Nat := 0
  deriving Repr, Inhabited

/-- A pure, total parser combinator. -/
abbrev ParserFn := IxParserContext → ParserState → ParserState

end Ix.Frontend.Parser
