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

/-- Balanced binary segment tree over character suffixes `(ch, byteOffset, tailChars)`,
    providing $O(\log N)$ random access by character index without `Array`/`Fin` proof terms. -/
inductive CharSegTree where
  | empty : CharSegTree
  | leaf  : Char → Nat → List Char → CharSegTree
  | node  : Nat → CharSegTree → CharSegTree → CharSegTree
  deriving Repr, Inhabited

/-- Pure input context that pre-decodes `input` into a spine of characters `chars`,
    cumulative UTF-8 byte offsets `byteOffsets`, `charCount`, `byteSize`, and an
    $O(\log N)$ `CharSegTree`. -/
structure InputContext where
  fileName    : String
  input       : String
  chars       : List Char
  byteOffsets : List Nat
  charCount   : Nat
  byteSize    : Nat := 0
  tree        : CharSegTree := .empty
  deriving Repr, Inhabited

namespace InputContext

/-- Build a balanced binary tree over `count` suffixes of `cs` and `os` in $O(N)$ steps,
    structurally recursive on `depth : Nat` (compiled directly to `Nat.rec`). -/
def buildCharSegTreeAux : Nat → Nat → List Char → List Nat → (CharSegTree × List Char × List Nat)
  | 0, _, cs, os => (.empty, cs, os)
  | depth + 1, count, cs, os =>
    if Nat.beq count 0 then
      (.empty, cs, os)
    else if Nat.beq count 1 then
      match cs, os with
      | c :: cs', o :: os' => (.leaf c o (c :: cs'), cs', os')
      | _, _               => (.empty, cs, os)
    else
      let leftLen := count / 2
      let rightLen := count - leftLen
      match buildCharSegTreeAux depth leftLen cs os with
      | (leftTree, cs1, os1) =>
        match buildCharSegTreeAux depth rightLen cs1 os1 with
        | (rightTree, cs2, os2) =>
          (.node leftLen leftTree rightTree, cs2, os2)

/-- Look up character index `idx` in `CharSegTree` in $O(\log N)$ steps. -/
def lookupSegTree : CharSegTree → Nat → Option (Char × Nat × List Char)
  | .empty, _ => none
  | .leaf c o tail, 0 => some (c, o, tail)
  | .leaf _ _ _, _ => none
  | .node leftLen left right, idx =>
    if Nat.ble (idx + 1) leftLen then
      lookupSegTree left idx
    else
      lookupSegTree right (idx - leftLen)

/-- UTF-8 byte length of a single Unicode scalar `Char`, computed via `Nat.ble` without `BitVec`. -/
def charUtf8ByteSize (c : Char) : Nat :=
  let n := c.val.toNat
  if Nat.ble n 0x7F then 1
  else if Nat.ble n 0x7FF then 2
  else if Nat.ble n 0xFFFF then 3
  else 4

/-- Reverse `revOffs` via `List` structural recursion. -/
def reverseNatList : List Nat → List Nat → List Nat
  | [], acc => acc
  | o :: os, acc => reverseNatList os (o :: acc)

/-- Compute `(byteOffsets, charCount, byteSize)` directly from `input.toList` in $O(N)$
    structural recursion on `List Char` — zero `String.toByteArray` or `Char.ofNat`! -/
def buildInputOffsets : List Char → Nat → List Nat → Nat → (List Nat × Nat × Nat)
  | [], byteAcc, revOffs, cnt =>
    (reverseNatList (byteAcc :: revOffs) [], cnt, byteAcc)
  | c :: cs, byteAcc, revOffs, cnt =>
    let bLen := charUtf8ByteSize c
    buildInputOffsets cs (byteAcc + bLen) (byteAcc :: revOffs) (cnt + 1)

/-- Construct an `InputContext` from a source string and optional file name. -/
def mkInputContext (input : String) (fileName : String := "<input>") : InputContext :=
  let chars := input.toList
  match buildInputOffsets chars 0 [] 0 with
  | (byteOffsets, charCount, byteSize) =>
    match buildCharSegTreeAux 20 charCount chars byteOffsets with
    | (tree, _, _) =>
      { fileName, input, chars, byteOffsets, charCount, byteSize, tree }

/-- Total number of Unicode scalar characters in the input. -/
def size (c : InputContext) : Nat :=
  c.charCount

/-- True when character index `idx` is at or past the end of input. -/
def atEnd (c : InputContext) (idx : Nat) : Bool :=
  idx ≥ c.charCount

/-- Return the character suffix `c.chars.drop idx` in $O(\log N)$ steps via `c.tree`. -/
def charsFrom (c : InputContext) (idx : Nat) : List Char :=
  match lookupSegTree c.tree idx with
  | some (_, _, tail) => tail
  | none              => []

/-- Return the character at character index `idx`, if in bounds, in $O(\log N)$ steps. -/
def get? (c : InputContext) (idx : Nat) : Option Char :=
  match lookupSegTree c.tree idx with
  | some (ch, _, _) => some ch
  | none            => none

/-- Return the character at character index `idx`, or `default` if out of bounds, in $O(\log N)$ steps. -/
def getD (c : InputContext) (idx : Nat) (default : Char := '\x00') : Char :=
  match lookupSegTree c.tree idx with
  | some (ch, _, _) => ch
  | none            => default

/-- Convert a character index `idx` into its UTF-8 byte position in `c.input` in $O(\log N)$ steps. -/
def bytePos (c : InputContext) (idx : Nat) : Nat :=
  match lookupSegTree c.tree idx with
  | some (_, off, _) => off
  | none             => c.byteSize

/-- Build an `Ix.Substring` spanning character indices `[startIdx, stopIdx)`. -/
def substring (c : InputContext) (startIdx stopIdx : Nat) : Ix.Substring :=
  { str      := c.input
    startPos := c.bytePos startIdx
    stopPos  := c.bytePos stopIdx }

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

def isEmpty (s : SyntaxStack) : Bool := s.len == 0

def push (s : SyntaxStack) (stx : Ix.Syntax) : SyntaxStack :=
  { rev := stx :: s.rev, len := s.len + 1 }

def pop (s : SyntaxStack) : SyntaxStack :=
  match s.rev with
  | _ :: xs => { rev := xs, len := s.len - 1 }
  | []      => { rev := [], len := 0 }

def back (s : SyntaxStack) : Ix.Syntax :=
  match s.rev with
  | x :: _ => x
  | []     => .missing

def getD (s : SyntaxStack) (i : Nat) : Ix.Syntax :=
  if i ≥ s.len then .missing
  else Syntax.listGetD s.rev (s.len - 1 - i) .missing

/-- Pop `n` elements from the top of `rev`, accumulating them in left-to-right order in `acc`. -/
def popTopN : Nat → List Ix.Syntax → List Ix.Syntax → List Ix.Syntax × List Ix.Syntax
  | 0, rev, acc           => (acc, rev)
  | _, [], acc            => (acc, [])
  | n + 1, x :: rest, acc => popTopN n rest (x :: acc)

def shrink (s : SyntaxStack) (newSize : Nat) : SyntaxStack :=
  if s.len ≤ newSize then s
  else
    let (_, rest) := popTopN (s.len - newSize) s.rev []
    { rev := rest, len := newSize }

def extract (s : SyntaxStack) (start stop : Nat) : Array Ix.Syntax :=
  let clampedStop := Nat.min stop s.len
  if clampedStop ≤ start then #[]
  else
    let afterStop := s.rev.drop (s.len - clampedStop)
    let (items, _) := popTopN (clampedStop - start) afterStop []
    items.toArray

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
  if e2.pos > e1.pos then e2
  else if e1.pos > e2.pos then e1
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

def bindState (s : ParserState) (k : ParserState → α) : α :=
  match s with
  | ⟨⟨rev, len⟩, lhsPrec, pos, cache, err⟩ =>
    match len, pos, err with
    | 0, 0, none => k ⟨⟨rev, 0⟩, lhsPrec, 0, cache, none⟩
    | 0, p, none => k ⟨⟨rev, 0⟩, lhsPrec, p, cache, none⟩
    | l, p, none => k ⟨⟨rev, l⟩, lhsPrec, p, cache, none⟩
    | l, p, some e => k ⟨⟨rev, l⟩, lhsPrec, p, cache, some e⟩

def hasError (s : ParserState) : Bool :=
  s.errorMsg.isSome

def stackSize (s : ParserState) : Nat :=
  s.stxStack.size

def restore (s : ParserState) (iniSz : Nat) (iniPos : Nat) : ParserState :=
  { s with
    stxStack := s.stxStack.shrink iniSz
    pos      := iniPos
    errorMsg := none }

def setPos (s : ParserState) (pos : Nat) : ParserState :=
  { s with pos := pos }

def pushSyntax (s : ParserState) (stx : Ix.Syntax) : ParserState :=
  { s with stxStack := s.stxStack.push stx }

def popSyntax (s : ParserState) : ParserState :=
  { s with stxStack := s.stxStack.pop }

def shrinkStack (s : ParserState) (iniSz : Nat) : ParserState :=
  { s with stxStack := s.stxStack.shrink iniSz }

def mkNode (s : ParserState) (k : Ix.Name) (iniSz : Nat) : ParserState :=
  match s with
  | ⟨stack, lhsPrec, pos, cache, err⟩ =>
    if err.isSome && stack.len == iniSz then
      ⟨stack.push .missing, lhsPrec, pos, cache, err⟩
    else
      let count := stack.len - iniSz
      let (children, restRev) := SyntaxStack.popTopN count stack.rev []
      let newStack : SyntaxStack := { rev := Syntax.mkNode k children.toArray :: restRev, len := iniSz + 1 }
      ⟨newStack, lhsPrec, pos, cache, err⟩

def mkTrailingNode (s : ParserState) (k : Ix.Name) (iniSz : Nat) (lhsPrec : Nat) : ParserState :=
  match s with
  | ⟨stack, _, pos, cache, err⟩ =>
    let baseSz := iniSz - 1
    let count := stack.len - baseSz
    let (children, restRev) := SyntaxStack.popTopN count stack.rev []
    let newStack : SyntaxStack := { rev := Syntax.mkNode k children.toArray :: restRev, len := baseSz + 1 }
    ⟨newStack, lhsPrec, pos, cache, err⟩

def setError (s : ParserState) (e : ParserError) : ParserState :=
  { s with errorMsg := some e }

def mkError (s : ParserState) (expected : String) : ParserState :=
  { s with
    stxStack := s.stxStack.push .missing
    errorMsg := some { pos := s.pos, expected := [expected] } }

def mkUnexpectedError (s : ParserState) (msg : String) (expected : List String := []) : ParserState :=
  { s with errorMsg := some { pos := s.pos, unexpected := msg, expected := expected } }

def mkEOIError (s : ParserState) (expected : List String := []) : ParserState :=
  s.mkUnexpectedError "unexpected end of input" expected

def mkErrorAt (s : ParserState) (expected : String) (pos : Nat) (iniSz : Nat) : ParserState :=
  let s := s.shrinkStack iniSz
  let s := s.pushSyntax .missing
  { s with pos := pos, errorMsg := some { pos := pos, expected := [expected] } }

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

/-- Reader context for `ParserFn`. -/
structure IxParserContext where
  inputCtx : InputContext
  env      : IxParserEnv
  prec     : Nat := 0
  deriving Repr, Inhabited

/-- A pure, total parser combinator. -/
abbrev ParserFn := IxParserContext → ParserState → ParserState

end Ix.Frontend.Parser
