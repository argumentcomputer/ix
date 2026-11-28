/-! # `strip-contracts`: the plain twin of an annotated source

The ownership suite pairs each annotated Lean source with its plain twin. The twin is the annotated
text with ix's scoped `@`-prefixed mode syntax deleted, so the two differ by construction only in
contracts:

* the import of ix's elaborator (`import Ix.Compile.SourceContract.Elab`),
  `open scoped Ix.Modes`, and the blank line after them;
* binder and constructor/structure field prefix modes: one or more `@erased`,
  `@once`, `@unique`, `@borrowed` or `@shared` keywords right after an opening
  `(`, `{`, `[` or `⦃`, each followed by a space, before a binder name
  (`(@erased _h : True)`, `{@erased α : Type}`, `(@unique @borrowed xs : List Nat)`,
  `(@shared x : Nat)`);
* result and arrow modes: one or more `@erased`, `@once`, `@unique` or `@borrowed`
  keywords right after `: `, `→ `, `-> ` or `, ` (after `∀ ...`), each followed by
  a space, before a type (`: @unique List Nat`, `A → @borrowed B`);
* `let` mode prefixes: `let @borrow v : T := …` (or `let @unique x := …`,
  `let @once @borrowed x : T := …`, etc.) becomes the ordinary `let v : T := …`;
* indented structure simple-field modes: `@shared f : T` or `@erased h : True`
  at the start of an indented field line becomes `f : T` / `h : True`.

Comments and strings are not special-cased: the fixture sources keep their
contract syntax out of comments. `tests-own` checks that every committed
`Plain.lean` is `strip` of its `Annotated.lean`. -/

namespace IxCCTests.Own.Strip

def elabImport : String := "import Ix.Compile.SourceContract.Elab"
def modesOpen : String := "open scoped Ix.Modes"

def binderKeywords : List String := ["erased", "once", "unique", "borrowed", "shared"]
def resultKeywords : List String := ["erased", "once", "unique", "borrowed"]
def letKeywords : List String := ["borrow", "borrowed", "unique", "once", "erased"]
def fieldKeywords : List String := ["shared", "erased"]

def isOpen (c : Char) : Bool := c == '(' || c == '{' || c == '[' || c == '⦃'

def isBinderStart (c : Char) : Bool := c.isAlpha || c == '_' || c.toNat ≥ 0x80

def isTypeStart (c : Char) : Bool :=
  isBinderStart c || c == '(' || c == '{' || c == '[' || c == '⦃'

/-- Match one `@<kw> ` prefix where `<kw>` is in `kws`, returning its character length. -/
def matchModeKw (kws : List String) : List Char → Option Nat
  | '@' :: rest =>
    kws.findSome? fun kw =>
      let kcs := kw.toList
      if rest.take kcs.length == kcs && rest[kcs.length]? == some ' ' then
        some (1 + kcs.length + 1)
      else none
  | _ => none

/-- Total character length of one or more `@<kw> ` prefixes at the front of `cs`,
when followed by a character satisfying `isFollow`. -/
def modeRun (kws : List String) (isFollow : Char → Bool) (cs : List Char) : Option Nat :=
  go cs.length cs 0
where
  go : Nat → List Char → Nat → Option Nat
    | 0, _, _ => none
    | fuel + 1, cur, acc =>
      match matchModeKw kws cur with
      | some n => go fuel (cur.drop n) (acc + n)
      | none =>
        if acc > 0 && (cur.head?.map isFollow).getD false then some acc else none

/-- Delete the scoped `@`-mode syntax of one line. -/
partial def stripLine (line : String) : String :=
  String.ofList (go line.toList [])
where
  go : List Char → List Char → List Char
    | [], acc => acc.reverse
    | c :: rest, acc =>
      if isOpen c then
        match modeRun binderKeywords isBinderStart rest with
        | some n => go (rest.drop n) (c :: acc)
        | none => go rest (c :: acc)
      else if (c == ':' || c == '→' || c == ',') && rest.head? == some ' ' then
        match modeRun resultKeywords isTypeStart (rest.drop 1) with
        | some n => go (rest.drop (1 + n)) (' ' :: c :: acc)
        | none => go rest (c :: acc)
      else if c == '-' && rest.take 2 == ['>', ' '] then
        match modeRun resultKeywords isTypeStart (rest.drop 2) with
        | some n => go (rest.drop (2 + n)) (' ' :: '>' :: '-' :: acc)
        | none => go rest (c :: acc)
      else if c == 'l' && rest.take 3 == "et ".toList &&
          (acc.isEmpty || acc.head!.isWhitespace || acc.head! == '(') then
        let tail := rest.drop 3
        match modeRun letKeywords isBinderStart tail with
        | some n => go (tail.drop n) ("let ".toList.reverse ++ acc)
        | none => go rest (c :: acc)
      else if c == '@' && !acc.isEmpty && acc.all (· == ' ') && rest.contains ':' then
        match modeRun fieldKeywords isBinderStart (c :: rest) with
        | some n => go ((c :: rest).drop n) acc
        | none => go rest (c :: acc)
      else go rest (c :: acc)

/-- The plain twin of an annotated source. -/
def strip (src : String) : String :=
  let lines := src.splitOn "\n"
  let lines := match lines with
    | l1 :: l2 :: "" :: rest =>
      if l1 == elabImport && l2 == modesOpen then rest else lines
    | _ => lines
  let lines := match lines with
    | l1 :: l2 :: rest =>
      if l1 == elabImport && l2 == modesOpen then rest
      else if l1 == elabImport && l2 == "" then rest
      else if l1 == modesOpen && l2 == "" then rest
      else lines
    | _ => lines
  "\n".intercalate (lines.map stripLine)

/-- Explicit output oracles, including ordinary syntax which must not change. -/
def regressionCases : List (String × String) := [
  ("def pick (@erased _h : True) (n : Nat) : Nat := n + 1",
   "def pick (_h : True) (n : Nat) : Nat := n + 1"),
  ("def len {@erased α : Type} (xs : List α) : Nat := 0",
   "def len {α : Type} (xs : List α) : Nat := 0"),
  ("def localId (@borrowed x : Nat) : @borrowed Nat := x",
   "def localId (x : Nat) : Nat := x"),
  ("def f (@unique @borrowed xs : List Nat) : @unique @borrowed (List Nat) := xs",
   "def f (xs : List Nat) : (List Nat) := xs"),
  ("def g (f : (@once x : Nat) → @unique Nat) : Nat -> @borrowed Nat := f",
   "def g (f : (x : Nat) → Nat) : Nat -> Nat := f"),
  ("def h : ∀ (@unique x : Nat), @unique Nat := id",
   "def h : ∀ (x : Nat), Nat := id"),
  ("  let @borrow v : List Nat := owner",
   "  let v : List Nat := owner"),
  ("  let @borrow view := owner",
   "  let view := owner"),
  ("  let @unique @borrowed view : (List Nat) := xs",
   "  let view : (List Nat) := xs"),
  ("  @shared payload : List Nat",
   "  payload : List Nat"),
  ("  | node (@shared l : Tree) (@erased h : True) : Tree",
   "  | node (l : Tree) (h : True) : Tree"),
  ("let (v : List Nat) := xs",
   "let (v : List Nat) := xs"),
  ("let v := xs",
   "let v := xs"),
  ("def f := (1 + 2)",
   "def f := (1 + 2)"),
  ("def g := @id Nat 3",
   "def g := @id Nat 3"),
  ("def h := (@id Nat) 3",
   "def h := (@id Nat) 3")]

end IxCCTests.Own.Strip
