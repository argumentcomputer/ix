/-
  Tests for the Ixon text-format parser and printer.

  Direct port of the Rust unit suite (`crates/ixon/src/syntax/mod.rs`
  tests) — same corpus strings, same expected canonical output. Until
  the FFI parity externs land (plan M4), these shared goldens are the
  cross-language behavioral check: both implementations must print
  byte-identical canonical text for these inputs.

  Also includes SlimCheck properties mirroring the Rust quickcheck
  suite (`crates/ixon/src/syntax/props.rs`): printer fixpoint over
  arbitrary valid ASTs, node-count/byte bound, and totality on fuzzed
  and mutated input. Generators/shrinkers live in
  `Tests/Gen/IxonSyntax.lean`. (Parse determinism, a Rust property,
  is definitional here — the parsers are pure functions.)
-/
module

public import LSpec
public import Ix.IxonSyntax
public import Tests.Gen.IxonSyntax

open LSpec Ixon.Syntax

namespace Tests.IxonSyntax

/-- Text-level roundtrip: parse, print, reparse, reprint; the two
    prints must agree. Returns the canonical form. -/
def roundtripTerm (src : String) : Except String String := do
  let t1 ← (parseTerm src).mapError fun e => s!"parse failed on {repr src}: {e}"
  let p1 := printTerm t1
  let t2 ← (parseTerm p1).mapError fun e => s!"reparse failed on {repr p1}: {e}"
  let p2 := printTerm t2
  if p1 == p2 then return p1
  else throw s!"not a fixpoint for {repr src}: {repr p1} vs {repr p2}"

def roundtripFile (src : String) : Except String String := do
  let f1 ← (parseFile src).mapError fun e => s!"parse failed: {e}\n---\n{src}"
  let p1 := printFile f1
  let f2 ← (parseFile p1).mapError fun e => s!"reparse failed: {e}\n---\n{p1}"
  let p2 := printFile f2
  if p1 != p2 then throw s!"printer not a fixpoint:\n--- p1\n{p1}\n--- p2\n{p2}"
  else if f1.decls.size != f2.decls.size then throw "decl count changed"
  else return p1

/-- Render an `Except String` check as a test. -/
def checkExcept (name : String) : Except String α → TestSeq
  | .ok _ => test name true
  | .error e => test s!"{name}: {e}" false

/-- Does the result satisfy the predicate? (`test` needs applied Bool
    functions, not literal `match` bodies, for `Testable`.) -/
def isOk (r : Except ε α) (p : α → Bool) : Bool :=
  match r with
  | .ok a => p a
  | .error _ => false

/-- Does the parse print to exactly `s`? -/
def printsTo (r : Except SyntaxError Term) (s : String) : Bool :=
  isOk r (printTerm · == s)

/-- Does the roundtrip yield exactly `expect`? -/
def rtEq (src expect : String) : Bool :=
  match roundtripTerm src with
  | .ok p => p == expect
  | .error _ => false

def errKind (r : Except SyntaxError α) (p : ErrorKind → Bool) : Bool :=
  match r with
  | .error e => p e.kind
  | .ok _ => false

def errLine (r : Except SyntaxError α) (n : Nat) : Bool :=
  match r with
  | .error e => e.line == n
  | .ok _ => false

/-- The term corpus — identical to the Rust `term_roundtrips` list. -/
def termCorpus : List String := [
  "Nat",
  "Nat.add",
  "Nat.add x y",
  "f (g x) y",
  "(f x) y z",
  "fun (x : Nat) => x",
  "fun (x y : Nat) (z : Bool) => f x z",
  "fun {α : Type u} (a : α) => a",
  "fun [inst : Monad m] => inst",
  "fun ⦃p : Prop⦄ => p",
  "(x : Nat) → Vec x",
  "(x y : Nat) (z : Bool) → f x y z",
  "Nat → Bool",
  "Nat → Bool → Prop",
  "(Nat → Bool) → Prop",
  "let x : Nat := 5; f x",
  "have h : And p q := trivial; h",
  "let f : Nat → Nat := fun (x : Nat) => x; f 3",
  "Prop",
  "Type",
  "Type 1",
  "Type u",
  "Type (max u v)",
  "Sort (u + 1)",
  "Sort (imax u v)",
  "List.{0} Nat",
  "Except.ok.{0, 0} PatchError String s",
  "Nat.add_comm#deadbeef",
  "#deadbeef",
  "#deadbeef.{u} x",
  "proj Prod 0 p",
  "proj #abcd1234 1 (mk x y)",
  "42",
  "0xff",
  "\"hello\"",
  "\"line\\nbreak \\\"quoted\\\"\"",
  "«weird name».foo",
  "Nat.«0».bar",
  "f Nat.0.bar",
  "α.«β»",
  "f _x y'",
  "x!? y"
]

def termRoundtrips : TestSeq :=
  termCorpus.foldl (init := .done) fun acc src =>
    acc ++ checkExcept s!"roundtrip {repr src}" (roundtripTerm src)

def isPinnedRef : Term → Bool
  | .ref r => r.hash.isSome
  | _ => false

def isUnaryApp : Term → Bool
  | .app _ args _ => args.size == 1
  | _ => false

def isLet (nonDep : Bool) : Term → Bool
  | .letE nd .. => nd == nonDep
  | _ => false

def adjacencyIsSignificant : TestSeq :=
  let pinned := parseTerm "f#abcd"
  let applied := parseTerm "f #abcd"
  test "f#abcd is a pinned ref" (isOk pinned isPinnedRef)
  ++ test "f #abcd is an application" (isOk applied isUnaryApp)
  ++ test "pinned prints f#abcd" (printsTo pinned "f#abcd")
  ++ test "applied prints f #abcd" (printsTo applied "f #abcd")

def typeArgumentIsGreedy : TestSeq :=
  test "f Type 1 takes 1 as universe arg"
    (isOk (parseTerm "f Type 1") isUnaryApp)
  ++ test "f (Type) 1 canonical" (rtEq "f (Type) 1" "f (Type) 1")
  ++ test "f Type 1 canonical" (rtEq "f Type 1" "f (Type 1)")

def letVsHave : TestSeq :=
  test "let is dependent"
    (isOk (parseTerm "let x : N := v; x") (isLet false))
  ++ test "have is non-dependent"
    (isOk (parseTerm "have x : N := v; x") (isLet true))

/-- The acceptance fixture: hand-formatted input normalizes to the
    SAME canonical bytes the Rust printer emits (shared golden). -/
def acceptanceFixture : TestSeq :=
  let src := "ixon 1\n"
    ++ "import #9c41aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa9c41\n"
    ++ "\n"
    ++ "def : String → Except PatchError String :=\n"
    ++ "  fun (s : String) => Except.ok PatchError String s\n"
  let canonical :=
    "import #9c41aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa9c41\n"
    ++ "\n"
    ++ "def : String → Except PatchError String := "
    ++ "fun (s : String) => Except.ok PatchError String s\n"
  match roundtripFile src with
  | .error e => test s!"acceptance fixture: {e}" false
  | .ok printed =>
    test "acceptance fixture prints the shared canonical golden"
      (printed == canonical)

def kitchenSink : TestSeq :=
  let src := "ixon 1

import #aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
import Std.V2#bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb

def id.{u} : (α : Sort u) → α → α := fun (α : Sort u) (a : α) => a

theorem trivial : True := True.intro

unsafe opaque magic : Nat := 0

partial def loop : Nat → Nat := fun (n : Nat) => loop n

axiom choice.{u} : (α : Sort u) → Nonempty α → α

quot type Quot.{u} : (α : Sort u) → (α → α → Prop) → Sort u

inductive Nat' (params := 0) (indices := 0) : Type where
  | zero (params := 0) (fields := 0) : Nat'
  | succ (params := 0) (fields := 1) : Nat' → Nat'

recursor Nat'.rec.{u} (params := 0) (indices := 0) (motives := 1) (minors := 2) :
    (motive : Nat' → Sort u) → motive Nat'.zero →
    ((n : Nat') → motive n → motive (Nat'.succ n)) → (t : Nat') → motive t where
  | rule (fields := 0) := z
  | rule (fields := 1) := fun (n : Nat') (ih : motive n) => s n ih

mutual
def even : Nat → Bool := fun (n : Nat) => odd n
def odd : Nat → Bool := fun (n : Nat) => even n
end

dprj even := #cccccccccccccccccccccccccccccccc 0
cprj Nat'.succ := #dddd 0 1

⊢ even (succ zero) : Bool
"
  checkExcept "kitchen sink roundtrip" (roundtripFile src)
  ++ test "kitchen sink has a main expression"
    (isOk (parseFile src) (·.main.isSome))

def rtFileEq (src expect : String) : Bool :=
  match roundtripFile src with
  | .ok p => p == expect
  | .error _ => false

def mainExpression : TestSeq :=
  test "minimal main-only file is canonical (no header)"
    (rtFileEq "⊢ 1 : Nat\n" "⊢ 1 : Nat\n")
  ++ test "explicit ixon 1 header accepted and canonically omitted"
    (rtFileEq "ixon 1\n⊢ 1 : Nat\n" "⊢ 1 : Nat\n")
  ++ test "ASCII turnstile normalizes to ⊢"
    (rtFileEq "|- 1 : Nat\n" "⊢ 1 : Nat\n")
  ++ test "low-precedence values parenthesize canonically"
    (rtFileEq "⊢ fun (x : Nat) => x : Nat → Nat\n"
      "⊢ (fun (x : Nat) => x) : Nat → Nat\n")
  ++ test "the annotation is mandatory"
    (errKind (parseFile "⊢ 1\n") fun k =>
      match k with
      | .unexpectedToken .. => true
      | _ => false)
  ++ test "bare form accepted as the file's sole item"
    (rtFileEq "1 : Nat\n" "⊢ 1 : Nat\n")
  ++ test "bare form after imports"
    (rtFileEq
      ("import "
        ++ "#aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\n"
        ++ "fun (x : Nat) => x : Nat → Nat\n")
      ("import "
        ++ "#aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\n\n"
        ++ "⊢ (fun (x : Nat) => x) : Nat → Nat\n"))
  ++ test "leading ixon without a numeral is content"
    (rtFileEq "ixon : Nat\n" "⊢ ixon : Nat\n")
  ++ test "the fully minimal wire: one bare judgment"
    (rtFileEq
      ("fun (s : String) => Except.ok PatchError String s : "
        ++ "String -> Except PatchError String\n")
      ("⊢ (fun (s : String) => Except.ok PatchError String s) : "
        ++ "String → Except PatchError String\n"))
  ++ test "after a declaration the turnstile is required"
    (errKind (parseFile "ixon 1\ndef x : N := v\n1 : Nat\n") fun k =>
      match k with
      | .unexpectedToken .. => true
      | _ => false)
  ++ test "at most one main expression"
    (errKind (parseFile "ixon 1\n⊢ 1 : Nat ⊢ 2 : Nat\n")
      (· == .mainExprNotLast))
  ++ test "main expression must be last"
    (errKind (parseFile "ixon 1\n⊢ 1 : Nat def x : A := b\n")
      (· == .mainExprNotLast))

def mainAfterTermFinalDecl : TestSeq :=
  -- Regression (found by quickcheck on the Rust side): the turnstile
  -- stops the preceding declaration's application spine.
  checkExcept "main after where-less inductive"
    (roundtripFile
      "ixon 1\ninductive N (params := 0) (indices := 0) : Prop\n\n⊢ Prop : Prop\n")
  ++ checkExcept "|- after a ctor block is not eaten by the bar"
    (roundtripFile
      ("ixon 1\ninductive N (params := 0) (indices := 0) : Prop where\n"
        ++ "  | c (params := 0) (fields := 0) : N\n|- c : N\n"))

def versionGate : TestSeq :=
  test "ixon 2 rejected"
    (errKind (parseFile "ixon 2\n") fun k => k == .unknownVersion 2 1)

def importHashLength : TestSeq :=
  test "short import hash rejected"
    (errKind (parseFile "ixon 1\nimport #abcd\n")
      fun k => k == .importHashLength 4)

def errorShapes : TestSeq :=
  test "missing => positioned"
    (errKind (parseTerm "fun (x : Nat) x") fun k =>
      match k with
      | .unexpectedToken expected _ => (expected.splitOn "=>").length > 1
      | _ => false)
  ++ test "uppercase hash rejected"
    (errKind (parseTerm "#DEAD") fun k =>
      match k with
      | .invalidHash _ => true
      | _ => false)
  ++ test "placeholder is not a term"
    (errKind (parseTerm "f _") (· == .placeholder))
  ++ test "(x : Nat) without arrow is committed"
    (errKind (parseTerm "(x : Nat)") fun k =>
      match k with
      | .unexpectedToken expected _ => (expected.splitOn "→").length > 1
      | _ => false)
  ++ test "empty levels"
    (errKind (parseTerm "Nat.{}") (· == .emptyLevels))
  ++ test "line/col are 1-based"
    (errLine (parseFile "ixon 1\ndef x : Nat :=\n") 3)

def depthCap : TestSeq :=
  let limits : Limits := { maxDepth := 16 }
  let deep := "".pushn '(' 64 ++ "x" ++ "".pushn ')' 64
  test "depth cap is a structured error"
    (errKind (parseTerm deep limits) fun k =>
      match k with
      | .capExceeded .depth _ => true
      | _ => false)

def byteCap : TestSeq :=
  let limits : Limits := { maxBytes := 8 }
  test "byte cap is a structured error"
    (errKind (parseTerm "f x y z w" limits) fun k =>
      match k with
      | .capExceeded .bytes _ => true
      | _ => false)

def commentsAndWhitespace : TestSeq :=
  test "comments are skipped"
    (printsTo (parseTerm "f -- line comment\n  /- block /- nested -/ -/ x")
      "f x")
  ++ test "unterminated block comment"
    (errKind (parseTerm "f /- open") (· == .unterminatedComment))

def reservedComponentsEscape : TestSeq :=
  test "Nat.«def» roundtrips"
    (printsTo (parseTerm "Nat.«def»") "Nat.«def»")
  ++ test "«123» stays Str"
    (printsTo (parseTerm "Foo.«123»") "Foo.«123»")
  ++ test "bare 123 is Num"
    (printsTo (parseTerm "Foo.123") "Foo.123")

/-! ## Properties (mirror `props.rs`) -/

open Tests.Gen.IxonSyntax

/-- `print ∘ parse ∘ print = print` at the term level. -/
def termFixpoint (t : Term) : Bool :=
  let p1 := printTerm t
  match parseTerm p1 with
  | .ok t2 => printTerm t2 == p1
  | .error _ => false

/-- `print ∘ parse ∘ print = print` at the file level. -/
def fileFixpoint (f : File) : Bool :=
  let p1 := printFile f
  match parseFile p1 with
  | .ok f2 => printFile f2 == p1
  | .error _ => false

/-- The metering claim on `Limits`: no ε-productions, so the parsed
    node count is bounded by the printed byte length. -/
def nodeCountBounded (t : Term) : Bool :=
  let p := printTerm t
  match parseTerm p with
  | .ok t2 => countTermNodes t2 ≤ p.utf8ByteSize
  | .error _ => false

/-- Force evaluation of a parse result (totality: a value or a
    structured error, never a runtime crash). -/
def forced (r : Except SyntaxError α) : Bool :=
  match r with
  | .ok _ => true
  | .error _ => true

/-- Totality on fuzzed input, both entry points. -/
def parseTotal (f : Fuzz) : Bool :=
  forced (parseTerm f.s) && forced (parseFile f.s)

/-- Caps are respected and total, even when tiny. -/
def tinyLimitsTotal (f : Fuzz) : Bool :=
  let tiny : Limits := { maxBytes := 64, maxNodes := 16, maxDepth := 4 }
  forced (parseTerm f.s tiny) && forced (parseFile f.s tiny)

/-- Near-valid fuzz: mutate chars of canonical output (drawn from the
    syntax-relevant pool), reparse, require totality. -/
def mutatedTotal (t : Term) (m : Muts) : Bool :=
  let chars := (printTerm t).toList.toArray
  if chars.isEmpty then true
  else
    let mutated := m.muts.foldl (init := chars) fun cs (pos, ci) =>
      cs.set! (pos % cs.size) fuzzChars[ci % fuzzChars.size]!
    let s := String.ofList mutated.toList
    forced (parseTerm s) && forced (parseFile s)

end Tests.IxonSyntax

open Tests.IxonSyntax Tests.Gen.IxonSyntax in
public def Tests.IxonSyntax.suite : List LSpec.TestSeq := [
  termRoundtrips,
  adjacencyIsSignificant,
  typeArgumentIsGreedy,
  letVsHave,
  acceptanceFixture,
  kitchenSink,
  mainExpression,
  mainAfterTermFinalDecl,
  versionGate,
  importHashLength,
  errorShapes,
  depthCap,
  byteCap,
  commentsAndWhitespace,
  reservedComponentsEscape,
  checkIO "term print∘parse∘print fixpoint" (∀ t : Term, termFixpoint t),
  checkIO "file print∘parse∘print fixpoint" (∀ f : File, fileFixpoint f),
  checkIO "node count ≤ printed bytes" (∀ t : Term, nodeCountBounded t),
  checkIO "parse total on fuzz strings" (∀ f : Fuzz, parseTotal f),
  checkIO "parse total under tiny limits" (∀ f : Fuzz, tinyLimitsTotal f),
  checkIO "mutated canonical text total"
    (∀ (t : Term) (m : Muts), mutatedTotal t m)
]
