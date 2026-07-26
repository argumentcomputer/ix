/-
  Structured errors for the Ixon text format (R8: errors are data).

  Behavioral mirror of `crates/ixon/src/syntax/error.rs`: same variant
  set, same rendering, same line/column convention (1-based; column
  counted in Unicode scalar values). The variant set is part of the
  cross-language parity surface.
-/
module

public import Ix.IxonSyntax.AST

public section

namespace Ixon.Syntax

/-- Which parser limit was exceeded. -/
inductive Cap where
  | bytes
  | nodes
  | depth
  deriving BEq, Repr, Inhabited

/-- Structured error kind (parse-stage variants; the resolve stage
    extends this later). Mirrors Rust `syntax::ErrorKind`. -/
inductive ErrorKind where
  | unexpectedToken (expected found : String)
  | unknownVersion (found supported : Nat)
  | capExceeded (which : Cap) (limit : Nat)
  | invalidHash (reason : String)
  | importHashLength (found : Nat)
  | invalidEscape
  | unterminatedString
  | unterminatedQuotedName
  | unterminatedComment
  | natOutOfRange
  | placeholder
  | emptyLevels
  | badMutualMember
  | mainExprNotLast
  deriving BEq, Repr, Inhabited

/-- A positioned, structured syntax error. -/
structure SyntaxError where
  kind : ErrorKind
  span : Span
  /-- 1-based line of `span.start`. -/
  line : Nat
  /-- 1-based column (in Unicode scalar values) of `span.start`. -/
  col : Nat
  deriving BEq, Repr, Inhabited

/-- Derive (1-based line, 1-based char column) for a byte offset. -/
def lineCol (src : String) (pos : Nat) : Nat × Nat :=
  go src.toList 0 1 1
where
  go : List Char → Nat → Nat → Nat → Nat × Nat
    | [], _, line, col => (line, col)
    | c :: cs, i, line, col =>
      if i ≥ pos then (line, col)
      else if c == '\n' then go cs (i + c.utf8Size) (line + 1) 1
      else go cs (i + c.utf8Size) line (col + 1)

/-- Build an error, deriving line/column from `src`. -/
def SyntaxError.new (kind : ErrorKind) (span : Span) (src : String)
    : SyntaxError :=
  let (line, col) := lineCol src (min span.start src.utf8ByteSize)
  { kind, span, line, col }

def ErrorKind.render : ErrorKind → String
  | .unexpectedToken expected found =>
    s!"expected {expected}, found {found}"
  | .unknownVersion found supported =>
    s!"unknown ixon version {found} (this parser speaks {supported})"
  | .capExceeded which limit =>
    let w := match which with
      | .bytes => "byte"
      | .nodes => "node"
      | .depth => "depth"
    s!"{w} limit exceeded (max {limit})"
  | .invalidHash reason => s!"invalid #hash reference: {reason}"
  | .importHashLength found =>
    s!"import hashes must be exactly 64 hex digits, found {found}"
  | .invalidEscape => "invalid string escape"
  | .unterminatedString => "unterminated string literal"
  | .unterminatedQuotedName => "unterminated «…» name component"
  | .unterminatedComment => "unterminated block comment"
  | .natOutOfRange => "numeric literal out of range for this position"
  | .placeholder => "`_` is not a term (the grammar has no holes)"
  | .emptyLevels => "`.{}` must list at least one universe"
  | .badMutualMember =>
    "only def/theorem/opaque, inductive, and recursor declarations "
      ++ "may appear in a mutual block"
  | .mainExprNotLast =>
    "a main expression (`⊢ value : type`) must be the last item "
      ++ "in the file"

instance : ToString SyntaxError where
  toString e := s!"{e.line}:{e.col}: {e.kind.render}"

end Ixon.Syntax
