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
  testArgs : List String
  benchArgs : List String
  expected : String
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
  return {
    name := ← str value "name", rung := ← str value "rung", variant := ← str value "variant"
    lean := ← str (← field value "lean") "path"
    testArgs := ← strs value "test_args", benchArgs := ← strs value "bench_args"
    expected := ← str value "expected"
    twin := { path := ← str twin "path", language := ← str twin "language",
              compile := ← strs twin "compile" } }

def Manifest.load (path : System.FilePath) : IO Manifest := do
  let json ← IO.ofExcept (Json.parse (← IO.FS.readFile path))
  IO.ofExcept do
    let lean ← field json "lean"
    return {
      leanCompile := ← strs lean "compile", leanLink := ← strs lean "link"
      fixtures := ← (← (← field json "fixtures").getArr?).mapM Fixture.parse }

/-- A measured implementation. `lean-clang` is the incumbent: the fixture's
Lean source through Lean's own compiler and bundled `leanc`/clang at `-O3`.
`clang-O2`/`clang-O3` compile the natural C or C++ twin. Compilatrix rows
join when the rebuilt pipeline compiles the fixtures. -/
inductive Row | leanClang | clangO2 | clangO3
  deriving BEq, Repr, Inhabited

def Row.all : List Row := [.leanClang, .clangO2, .clangO3]

def Row.name : Row → String
  | .leanClang => "lean-clang"
  | .clangO2 => "clang-O2"
  | .clangO3 => "clang-O3"

def Row.ofName? : String → Option Row
  | "lean-clang" => some .leanClang
  | "clang-O2" => some .clangO2
  | "clang-O3" => some .clangO3
  | _ => none

/-- Substitute `{src}`, `{out}` and `{c}` placeholders. -/
def expand (template : List String) (subst : List (String × String)) : List String :=
  template.map fun word => subst.foldl (fun w (k, v) => w.replace ("{" ++ k ++ "}") v) word

end Runner
