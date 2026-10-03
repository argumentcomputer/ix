import Lean.Data.Json

/-! The fixture manifest (`benchmarks/fixtures/manifest.json`) and the rows
the runner builds from it. -/

namespace Runner

open Lean

structure Twin where
  path : String
  language : String
  compile : List String

structure Fixture where
  name : String
  rung : String
  variant : String
  lean : String
  /-- The pure entry's name and type (`Nat → Nat → Nat`). -/
  entryName : String
  entryType : String
  testArgs : List String
  benchArgs : List String
  expected : String
  /-- The output at the bench arguments, where recorded. -/
  benchExpected : Option String
  twin : Twin

structure Manifest where
  leanCompile : List String
  leanLink : List String
  fixtures : Array Fixture

def field (value : Json) (key : String) : Except String Json := value.getObjVal? key
def str (value : Json) (key : String) : Except String String := do (← field value key).getStr?
def strs (value : Json) (key : String) : Except String (List String) := do
  (← (← field value key).getArr?).toList.mapM (·.getStr?)

def Fixture.parse (value : Json) : Except String Fixture := do
  let twin ← field value "twin"
  let entry ← field value "entry"
  return {
    name := ← str value "name", rung := ← str value "rung", variant := ← str value "variant"
    lean := ← str (← field value "lean") "path"
    entryName := ← str entry "name", entryType := ← str entry "type"
    testArgs := ← strs value "test_args", benchArgs := ← strs value "bench_args"
    expected := ← str value "expected"
    benchExpected := (str value "bench_expected").toOption
    twin := { path := ← str twin "path", language := ← str twin "language",
              compile := ← strs twin "compile" } }

def Manifest.load (path : System.FilePath) : IO Manifest := do
  let json ← IO.ofExcept (Json.parse (← IO.FS.readFile path))
  IO.ofExcept do
    let lean ← field json "lean"
    return {
      leanCompile := ← strs lean "compile", leanLink := ← strs lean "link"
      fixtures := ← (← (← field json "fixtures").getArr?).mapM Fixture.parse }

/-- The fixture's name as a C identifier (`sum-loop` ↦ `sum_loop`). -/
def Fixture.ident (f : Fixture) : String := f.name.map fun c => if c == '-' then '_' else c

/-- The entry's arity when every parameter and the result are `Nat`, which
the entry profile's adapters pass as scalars. -/
def Fixture.natArity? (f : Fixture) : Option Nat :=
  let parts := (f.entryType.splitOn "→").map (·.trimAscii.toString)
  if parts.length ≥ 2 && parts.length ≤ 6 && parts.all (· == "Nat") then some (parts.length - 1)
  else none

/-- A measured implementation.

* `lean-clang` is the incumbent: the fixture's Lean source through Lean's own
  compiler and bundled `leanc`/clang at `-O3`.
* `clang-O2`/`clang-O3` compile the natural C or C++ twin.
* `compilatrix` compiles the fixture's frozen Ixon closure
  (`fixtures/ixon-v4/bench-k1/<name>.ixe`, the closure of the same `entry`)
  with the `compilatrix` executable.
* Diagnostic rows, entry profile only, which attribute a gap and are never
  real-program results: `clang-tagged`, the K1 algorithms on compilatrix's
  value representation (tagged words, carry-checked `+ 1`) at `-O2`;
  `lir-kernel`, MEAS-4's hand-written Lir kernels (fib, sum-loop, gcd)
  through the current backend; and `compilatrix@NAME`, objects with the
  compilatrix row's interface from elsewhere (`build --variant NAME=DIR`,
  `DIR/<fixture>.o`): another commit's compiler, or a hand-edited
  what-if, measured against `compilatrix` in the same blocks. -/
inductive Row | leanClang | clangO2 | clangO3 | compilatrix | clangTagged | lirKernel
  | variant (name : String)
  deriving BEq, Repr, Inhabited

/-- The process profile's rows (each fixture's own program, whole-process time). -/
def Row.process : List Row := [.leanClang, .clangO2, .clangO3, .compilatrix]

/-- The entry profile's fixed rows (in-process repetitions); variants join
them where built. -/
def Row.entry : List Row := [.compilatrix, .lirKernel, .clangTagged, .leanClang, .clangO2, .clangO3]

def Row.all : List Row := [.leanClang, .clangO2, .clangO3, .compilatrix, .clangTagged, .lirKernel]

def variantPrefix : String := "compilatrix@"

def Row.name : Row → String
  | .leanClang => "lean-clang"
  | .clangO2 => "clang-O2"
  | .clangO3 => "clang-O3"
  | .compilatrix => "compilatrix"
  | .clangTagged => "clang-tagged"
  | .lirKernel => "lir-kernel"
  | .variant n => variantPrefix ++ n

def Row.ofName? (name : String) : Option Row :=
  match Row.all.find? (·.name == name) with
  | some r => some r
  | none =>
    if name.startsWith variantPrefix && name.length > variantPrefix.length then
      some (.variant (name.drop variantPrefix.length).toString)
    else none

def Row.diagnostic : Row → Bool
  | .clangTagged | .lirKernel | .variant _ => true
  | _ => false

/-- K1 fixtures whose natural twin the entry adapter calls, and which have a
tagged twin: the original five and the MT.2 corpus four. -/
def k1Twins : List String :=
  ["fib", "sum-loop", "ackermann", "tak", "gcd", "collatz", "prime-count", "even-odd", "sfib"]

/-- MEAS-4's hand-written Lir kernels: fixture name and object stem. -/
def lirKernels : List (String × String) := [("fib", "fib"), ("sum-loop", "sumLoop"), ("gcd", "gcd")]

/-- Substitute `{src}`, `{out}` and `{c}` placeholders. -/
def expand (template : List String) (subst : List (String × String)) : List String :=
  template.map fun word => subst.foldl (fun w (k, v) => w.replace ("{" ++ k ++ "}") v) word

end Runner
