/-! # `strip-contracts`: the plain twin of an annotated source (MT.7)

The ownership suite pairs each annotated Lean source with its plain twin
(`plans/fixtures/ownership-suite.md` §2.2). The twin is the annotated text
with ix's contract syntax deleted, so the two differ by construction only in
contracts:

* the import of ix's elaborator (`import Ix.Compile.SourceContract.Elab`)
  and the blank line after it;
* binder prefix atoms: a run of `0`, `1`, `&`, `!`, `~` right after an
  opening `(`, `{`, `[` or `⦃` and followed by a space (`(0 _h : True)`,
  `{0 α : Type}`, `(~! x : Nat)`);
* result and arrow contracts: a run of `!` and `~` after `: ` or `→ ` and
  followed by a space (`: ~ Nat`, `A → ! B`);
* `let borrow (~ x : T)` becomes the ordinary typed binder `let x : T`.

Comments and strings are not special-cased: the fixture sources keep their
contract syntax out of comments. `tests-own` checks that every committed
`Plain.lean` is `strip` of its `Annotated.lean`. -/

namespace IxCCTests.Own.Strip

def elabImport : String := "import Ix.Compile.SourceContract.Elab"

def isAtom (c : Char) : Bool := c == '0' || c == '1' || c == '&' || c == '!' || c == '~'

def isResultAtom (c : Char) : Bool := c == '!' || c == '~'

def isOpen (c : Char) : Bool := c == '(' || c == '{' || c == '[' || c == '⦃'

/-- The length of the run of `p` characters at the front of `cs`, when it
is non-empty and followed by a space and a name (a letter or `_`, so
`(1 + 2)` is left alone). -/
def atomRun (p : Char → Bool) (cs : List Char) : Option Nat :=
  let n := (cs.takeWhile p).length
  let name := match cs[n + 1]? with
    | some c => c.isAlpha || c == '_' || c.toNat ≥ 0x80
    | none => false
  if n > 0 && cs[n]? == some ' ' && name then some n else none

/-- Split the contents of one balanced parenthesized borrow binder. Nested
parentheses belong to its type and must survive. This tool handles fixture
syntax on one line, not arbitrary Lean tokens in strings or comments. -/
def borrowBinder : List Char → Nat → List Char → Option (List Char × List Char)
  | [], _, _ => none
  | ')' :: rest, 0, acc => some (acc.reverse, rest)
  | ')' :: rest, n + 1, acc => borrowBinder rest n (')' :: acc)
  | '(' :: rest, n, acc => borrowBinder rest (n + 1) ('(' :: acc)
  | c :: rest, n, acc => borrowBinder rest n (c :: acc)

/-- Delete the contract syntax of one line. -/
partial def stripLine (line : String) : String :=
  String.ofList (go line.toList [])
where
  go : List Char → List Char → List Char
    | [], acc => acc.reverse
    | c :: rest, acc =>
      if isOpen c then
        match atomRun isAtom rest with
        | some n => go (rest.drop (n + 1)) (c :: acc)
        | none => go rest (c :: acc)
      else if (c == ':' || c == '→') && rest.head? == some ' ' then
        match atomRun isResultAtom (rest.drop 1) with
        | some n => go (rest.drop (n + 2)) (' ' :: c :: acc)
        | none => go rest (c :: acc)
      else if c == 'l' && (rest.take 10) == "et borrow ".toList then
        let tail := rest.drop 10
        let binder := match tail with
          | '(' :: cs => do
            let (inside, after) ← borrowBinder cs 0 []
            if (after.dropWhile Char.isWhitespace).take 2 != ":=".toList then none
            else
              let inside := match atomRun isAtom inside with
                | some n => inside.drop (n + 1)
                | none => inside
              let name := inside.takeWhile fun (c : Char) =>
                c.isAlpha || c.isDigit || c == '_' || c.toNat ≥ 0x80
              let suffix := (inside.drop name.length).dropWhile Char.isWhitespace
              if name.isEmpty || suffix.head? != some ':' then none
              else some (inside ++ after)
          | _ => none
        go (binder.getD tail) ("let ".toList.reverse ++ acc)
      else go rest (c :: acc)

/-- The plain twin of an annotated source. -/
def strip (src : String) : String :=
  let lines := src.splitOn "\n"
  let lines := match lines with
    | l :: "" :: rest => if l == elabImport then rest else lines
    | _ => lines
  "\n".intercalate (lines.map stripLine)

/-- Explicit output oracles, including ordinary syntax which must not change. -/
def regressionCases : List (String × String) := [
  ("let borrow (~ v : List Nat) := xs", "let v : List Nat := xs"),
  ("  let borrow (~! view : (List Nat)) := xs", "  let view : (List Nat) := xs"),
  ("let borrow (~ f : (Nat → Nat)) := g", "let f : (Nat → Nat) := g"),
  ("let (v : List Nat) := xs", "let (v : List Nat) := xs"),
  ("let borrow (a, b) := pair", "let (a, b) := pair"),
  ("def f (! x : Nat) : ! Nat := x", "def f (x : Nat) : Nat := x"),
  ("def f := (1 + 2)", "def f := (1 + 2)"),
  ("let borrow v := xs", "let v := xs")]

end IxCCTests.Own.Strip
