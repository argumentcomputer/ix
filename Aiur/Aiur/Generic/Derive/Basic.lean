import Aiur.Generic.Runtime

/-! # Deriving a program's semantic helpers: what is rendered

The derivers (`Derive.Lookup`, `Derive.Mirrors`, `Derive.Obs`) read a prepared
program and render Lean declarations about it as text, which `Derive.Elab`
elaborates in place. They are untrusted: Lean checks every declaration they
render. `Target` says how the declarations name the program they are about. -/

namespace Aiur.Generic.Derive
open Aiur.Generic
open Aiur (Assertion BinOp Constant)

/-- **The program the derived declarations are about**, as they name it. -/
class Target (F : Type) where
  /-- A field element as the numeral that denotes it. -/
  toNat : F → Nat
  /-- The namespace whose `F` is the field type. -/
  fieldNamespace : String
  /-- The namespace of the emitted program: `functions`, `maps` and each function's constant
  (`Modules.emitProgram`). The lookup facts are declared there. -/
  program : String
  /-- The prepared source (a `Generic.Source`). -/
  source : String
  /-- A function's constant, relative to `program`. -/
  functionName : String → String
  /-- The namespace of the mirrors and their lemmas. -/
  mirrors : String
  /-- The namespace of the path inductives and their inversion theorems. -/
  obs : String
  /-- Mirrors that are written by hand, by function: the definition's text, and the
  definitions the function's mirror lemma unfolds besides it. -/
  mirrorOverrides : List (String × String × List String) := []
  /-- Functions whose mirror sequences with `bindPair` and `matchTuple` in place of `do` and
  `match`, for mirrors that are too large to unfold otherwise. -/
  mirrorPairBind : List String := []
  /-- Functions whose paths multiply: their path lemmas are derived under larger caps. -/
  obsGenerous : List String := []
  /-- The table of the path lemmas' names (`Derive.Obs`), if the program has one. -/
  obsNames : Option String := none

/-- **Parts.** What a derivation declares can be dealt out, in order, to `n` parts that
different modules elaborate side by side: a part `(i, n)` is the `i`-th of `n`, from 1.
`partOf n before total` is the part that holds the item at `before` of `total`. -/
def partOf (n before total : Nat) : Nat :=
  if total == 0 then 1 else min (n - 1) (before * n / total) + 1

variable {F : Type} [Target F]

def q (s : String) : String := s.quote

def list (xs : List String) : String := "[" ++ ", ".intercalate xs ++ "]"

def opt (r : α → String) : Option α → String
  | some x => s!"(some {r x})"
  | none => "none"

def bool (b : Bool) : String := if b then "true" else "false"

def field (x : F) : String := toString (Target.toNat x)

partial def ty : Ty → String
  | .field => ".field"
  | .tuple ts => s!"(.tuple {list (ts.map ty)})"
  | .array t n => s!"(.array {ty t} {n})"
  | .ptr t => s!"(.ptr {ty t})"
  | .param n => s!"(.param {q n})"
  | .named n args => s!"(.named {q n} {list (args.map ty)})"

def recordHead (h : RecordHead) : String :=
  s!"\{ type := {ty h.type}, fields := {list (h.fields.map q)}, rest := {bool h.rest}, " ++
    s!"params := {list (h.params.map q)}, slots := {opt (fun s => list (s.map (opt toString))) h.slots} }"

def fieldRef (f : FieldRef) : String :=
  s!"\{ name := {q f.name}, owner := {opt ty f.owner}, index := {f.index}, arity := {f.arity} }"

def updateStep : UpdateStep → String
  | .member f => s!"(.member {fieldRef f})"
  | .project i n => s!"(.project {i} {n})"
  | .index i n => s!"(.index {i} {n})"

def assertion (a : Assertion) : String :=
  s!"\{ message := {opt q a.message}, runtimeCheck := {bool a.runtimeCheck} }"

def builtin : Builtin → String
  | .ascribe t => s!"(.ascribe {ty t})"
  | .debug m => s!"(.debug {q m})"
  | .assertEq a => s!"(.assertEq {assertion a})"

def binOp : BinOp → String
  | .add => ".add" | .sub => ".sub" | .mul => ".mul" | .div => ".div"

/-- A function's constant, relative to the program's namespace. -/
def functionName (F : Type) [Target F] (symbol : String) : String :=
  Target.functionName (F := F) symbol

/-- A function's constant. -/
def functionConst (F : Type) [Target F] (symbol : String) : String :=
  s!"{Target.program F}.{functionName F symbol}"

def listLines (xs : List String) : String :=
  if xs.isEmpty then "[]" else "[\n    " ++ ",\n    ".intercalate xs ++ "]"

end Aiur.Generic.Derive
