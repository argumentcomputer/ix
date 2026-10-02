/-! # The kernel's layout, for the kernel fences

What the fences `kernel-layering` and `kernel-trust-surface` cover, and the
part each file of `Ix/Kernel/` belongs to, by its path. The table
`topLevel` is the one place to update when a top-level entry of
`Ix/Kernel/` is added, moved or removed: a file under an entry it does not
list fails both fences.

* **The checker** (`Part.checker`): the implementation, con-leche's
  `ConLeche/Kernel/*` (flattened into `Ix/Kernel/`), `Cached/*` and
  `Frontend/*`, with Ix's `LevelGeran.lean` beside `Level.lean`. It must
  never import the theory.
* **The theory** (`Part.theory`): everything else of the checker's
  correctness argument and its tools: `Verify`, `Semantics`, `SetTheory`,
  `SetModel`, `Term`, `Rules`, `Model` (the model lane), `Denotes`,
  `PinGen` and `MainTheorem`. Within it the layering fence tells apart the
  model lane (`Model{,/*}`), the capstone assembly (`MainTheorem`,
  `Verify/Cached{,/*}`) and the base (the rest).
* **Ix's boundary** (`Part.ix`): `Admission` (the certified entry), `Ref`,
  `Search`, `Audit`, `Ingress`, `Egress` and `Ixon`, Ix's modules between
  Ixon and the checker. The fences
  do not cover them, and the layering fence requires the checker and the
  theory never to import them: the boundary imports the kernel, never the
  other way round. They are fenced by Ix's Lean audits instead
  (`Ix/Kernel/Audit/*`), which see compiled code rather than tokens.

The fences cover every `Ix/Kernel/**/*.lean` in the first two parts; the
umbrella `Ix/Kernel.lean` sits outside `Ix/Kernel/`. Also here, the two
pieces of Python's text model the fences were first written against and
keep: universal-newline reading and Unicode whitespace. Tooling only:
nothing here is part of the certified closure. -/

namespace Tests.Ix.Kernel.KernelLayout

inductive Part where
  | checker
  | theory
  | ix
  deriving BEq, Repr

/-- Every top-level entry of `Ix/Kernel/` (a module stem: the file
`Ix/Kernel/X.lean` and the directory `Ix/Kernel/X/` alike), by part. -/
def topLevel : List (String × Part) := [
  -- the checker: con-leche's `ConLeche/Kernel/*`, flattened
  ("Basis", .checker), ("BasisA", .checker), ("BasisGen", .checker), ("Canon", .checker),
  ("Checker", .checker), ("CheckerBase", .checker), ("CheckerSplit", .checker),
  ("Core", .checker), ("CoreDefs", .checker), ("CoreIO", .checker), ("DeclCheck", .checker),
  ("Env", .checker), ("Exclusive", .checker), ("Expr", .checker), ("ExprOps", .checker),
  ("FEnv", .checker), ("Inductives", .checker), ("Level", .checker), ("LevelGeran", .checker),
  ("Name", .checker), ("NatOpPinSet", .checker), ("PropRead", .checker), ("PropWhen", .checker),
  ("StdAxioms", .checker), ("TrustAxioms", .checker), ("TrustPins", .checker),
  ("TypeChecker", .checker),
  -- the checker: con-leche's cached checker and frontend
  ("Cached", .checker), ("Frontend", .checker),
  -- the theory
  ("Denotes", .theory), ("MainTheorem", .theory), ("Model", .theory), ("PinGen", .theory),
  ("Rules", .theory), ("Semantics", .theory), ("SetModel", .theory), ("SetTheory", .theory),
  ("Term", .theory), ("Verify", .theory),
  -- Ix's boundary
  ("Admission", .ix), ("Audit", .ix), ("Egress", .ix), ("Ingress", .ix), ("Ixon", .ix), ("Ref", .ix),
  ("Search", .ix)]

def root : String := "Ix/Kernel/"

/-- `rest` without its first `n` characters. -/
def dropChars (s : String) (n : Nat) : String := String.ofList (s.toList.drop n)

/-- The top-level entry of a path under `Ix/Kernel/`: its first component,
without a `.lean` suffix. -/
def topEntry (path : String) : String :=
  let head := ((dropChars path root.length).splitOn "/").headD ""
  if head.endsWith ".lean" then String.ofList (head.toList.take (head.length - 5)) else head

/-- The part of a file under `Ix/Kernel/`, or `none` if `topLevel` does not
classify it. -/
def part? (path : String) : Option Part := topLevel.lookup (topEntry path)

/-- The model lane: `Ix/Kernel/Model{,/*}`. -/
def isModelLane (path : String) : Bool :=
  path == "Ix/Kernel/Model.lean" || path.startsWith "Ix/Kernel/Model/"

/-- The capstone assembly: `MainTheorem` and `Verify/Cached{,/*}`. -/
def isCapstone (path : String) : Bool :=
  path == "Ix/Kernel/MainTheorem.lean" || path == "Ix/Kernel/Verify/Cached.lean" ||
  path.startsWith "Ix/Kernel/Verify/Cached/"

/-- The rules tier: `Rules/*` and `Model/Rules/*`. -/
def isRulesTier (path : String) : Bool :=
  path.startsWith "Ix/Kernel/Rules/" || path.startsWith "Ix/Kernel/Model/Rules/"

/-- Every `.lean` file under `dir` (relative to the working directory),
recursively, sorted by code point. -/
def leanFilesUnder (dir : System.FilePath) : IO (Array String) := do
  unless ← dir.isDir do return #[]
  let mut files := #[]
  for path in ← dir.walkDir do
    if (path.fileName.getD "").endsWith ".lean" && !(← path.isDir) then
      files := files.push path.toString
  return files.qsort (· < ·)

/-- The files the fences cover (the checker and the theory), sorted, and the
files `topLevel` does not classify. -/
def covered : IO (Array String × Array String) := do
  let files ← leanFilesUnder "Ix/Kernel"
  return (files.filter (fun f => (part? f).any (· != .ix)), files.filter (part? · |>.isNone))

/-- Fail on files no entry of `topLevel` classifies. -/
def reportUnclassified (fence : String) (files : Array String) : IO Bool := do
  if files.isEmpty then return false
  IO.println s!"{fence} FAIL - files under Ix/Kernel/ that no part classifies ({files.size}):"
  for f in files do IO.println s!"    {f}"
  IO.println "    Add the file's top-level entry to `topLevel` in Tests/Ix/Kernel/KernelLayout.lean"
  IO.println "    (the checker, the theory, or Ix's boundary)."
  return true

/-- Python's `str.isspace` (and `re`'s `\s` on `str`). -/
def isPySpace (c : Char) : Bool :=
  let n := c.toNat
  (0x09 ≤ n && n ≤ 0x0d) || (0x1c ≤ n && n ≤ 0x20) || n == 0x85 || n == 0xa0 || n == 0x1680 ||
  (0x2000 ≤ n && n ≤ 0x200a) || n == 0x2028 || n == 0x2029 || n == 0x202f || n == 0x205f ||
  n == 0x3000

/-- Python's `str.strip()`. -/
def pyStrip (chars : List Char) : String :=
  String.ofList ((chars.dropWhile isPySpace).reverse.dropWhile isPySpace).reverse

/-- A text file read with universal newlines (`\r\n` and a lone `\r` read
as `\n`), as Python's `open(path).read()` reads it. -/
def readText (path : System.FilePath) : IO String := do
  let raw ← IO.FS.readFile path
  unless raw.contains '\r' do return raw
  let rec go : List Char → List Char → List Char
    | [], acc => acc.reverse
    | '\r' :: '\n' :: rest, acc => go rest ('\n' :: acc)
    | '\r' :: rest, acc => go rest ('\n' :: acc)
    | c :: rest, acc => go rest (c :: acc)
  return String.ofList (go raw.toList [])

end Tests.Ix.Kernel.KernelLayout
