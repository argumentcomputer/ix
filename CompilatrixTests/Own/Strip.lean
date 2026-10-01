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
* the `borrow` of `let borrow`.

Comments and strings are not special-cased: the fixture sources keep their
contract syntax out of comments. `tests-own` checks that every committed
`Plain.lean` is `strip` of its `Annotated.lean`. -/

namespace CompilatrixTests.Own.Strip

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
        go (rest.drop 10) ("let ".toList.reverse ++ acc)
      else go rest (c :: acc)

/-- The plain twin of an annotated source. -/
def strip (src : String) : String :=
  let lines := src.splitOn "\n"
  let lines := match lines with
    | l :: "" :: rest => if l == elabImport then rest else lines
    | _ => lines
  "\n".intercalate (lines.map stripLine)

end CompilatrixTests.Own.Strip
