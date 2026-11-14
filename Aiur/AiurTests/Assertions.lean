import Aiur.Generic
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Field.ZMod

namespace AiurAssertionTests
open Aiur
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000

def source : Generic.Program Nat := aiur% "
enum Inner { Empty, Pair(Field, Field) }
enum Outer { Empty, Some(Inner, [Field; 2]) }
struct Box<T> { value: T }
type Pair = (Field, Field);
fn fields(x: Field, y: Field) -> Field { assert_eq!(x, y, \"fields differ\"); x }
fn constrained(x: Field, y: Field) -> Field { constrain_eq!(x, y, \"fields differ\"); x }
fn tuples(x: Pair, y: Pair) -> () { assert_eq!(x, y); }
fn arrays(x: [Field; 2], y: [Field; 2]) -> () { assert_eq!(x, y,); }
fn constrained_arrays(x: [Field; 2], y: [Field; 2]) -> () { constrain_eq!(x, y,); }
fn enums(x: Outer, y: Outer) -> () { assert_eq!(x, y, \"nested enum\",); }
fn structs(x: Box<Pair>, y: Box<Pair>) -> () { assert_eq!(x, y); }
fn units() -> () { assert_eq!((), ()); assert_eq!(([]: [Field; 0]), []); }
fn loaded() -> Field {
  let p = &4; let q = &4;
  assert_eq!(*p, *q, \"contents\"); 9
}
fn ordered() -> Field { assert_eq!(*&3, *&3); 8 }
fn early() -> Field { assert_eq!(*&1, return 7, \"skipped\"); 0 }
fn skip() -> Field { match 0 { 0 => 5, _ => { assert_eq!(1, 2); 0 } } }
fn nested_failure() -> Field { debug!(\"before assertion\", 1); fields(1, 2) }
fn reduced() -> () { assert_eq!(0, 7); }
"

#guard (source.findFunction? "fields").any fun f => match f.body with
  | .letValue _ (.builtin (.assertEq ⟨some "fields differ", true⟩) [_, _]) _ => true
  | _ => false

#guard (source.findFunction? "constrained").any fun f => match f.body with
  | .letValue _ (.builtin (.assertEq ⟨some "fields differ", false⟩) [_, _]) _ => true
  | _ => false

def inner (x y : Rat) : SourceValue Rat := .construct "Inner" "Pair" [.field x, .field y]
def outer (x y : Rat) : SourceValue Rat := .construct "Outer" "Some" [inner x y, .tuple [3, 4]]
def empty : SourceValue Rat := .construct "Outer" "Empty" []
def box (x y : Rat) : SourceValue Rat :=
  .construct (Generic.Instance.symbol ⟨"Box", [.tuple [.field, .field]]⟩) Generic.structConstructor [.tuple [.field x, .field y]]
def failed (message : Option String := none) : Except String (SourceValue Rat × Heap Rat) :=
  .error (reprStr (EvalError.assertionFailed message))

def checks : List (String × List (SourceValue Rat) × Except String (SourceValue Rat × Heap Rat)) := [
  ("fields", [4, 4], .ok (4, [])), ("fields", [4, 5], failed (some "fields differ")),
  ("constrained", [4, 4], .ok (4, [])), ("constrained", [4, 5], failed (some "fields differ")),
  ("tuples", [.tuple [1, 2], .tuple [1, 2]], .ok (.tuple [], [])),
  ("tuples", [.tuple [1, 2], .tuple [2, 1]], failed),
  ("arrays", [.tuple [1, 2], .tuple [1, 2]], .ok (.tuple [], [])),
  ("arrays", [.tuple [1, 2], .tuple [1, 3]], failed),
  ("constrained_arrays", [.tuple [1, 2], .tuple [1, 2]], .ok (.tuple [], [])),
  ("constrained_arrays", [.tuple [1, 2], .tuple [1, 3]], failed),
  ("enums", [outer 1 2, outer 1 2], .ok (.tuple [], [])),
  ("enums", [outer 1 2, outer 1 3], failed (some "nested enum")),
  ("enums", [empty, outer 1 2], failed (some "nested enum")),
  ("enums", [empty, empty], .ok (.tuple [], [])),
  ("structs", [box 1 2, box 1 2], .ok (.tuple [], [])),
  ("structs", [box 1 2, box 2 1], failed),
  ("units", [], .ok (.tuple [], [])), ("loaded", [], .ok (9, [4, 4])),
  ("ordered", [], .ok (8, [3, 3])), ("early", [], .ok (7, [1])), ("skip", [], .ok (5, []))
]

run_cmd do
  let env ← Lean.getEnv
  for text in [
    "fn f() -> () { assert_eq!(&0, &0); }",
    "fn f() -> () { assert_eq!((1, &0), (1, &0)); }",
    "fn f() -> () { assert_eq!((&[0; 2]: &[Field; 2]), &[0; 2]); }",
    "fn f() -> () { let x: [&Field; 0] = []; assert_eq!(x, x); }",
    "enum E { Empty, Pointer(&Field) } fn f() -> () { assert_eq!(E::Empty, E::Empty); }",
    "struct S { p: &Field } fn f() -> () { let s = S { p: &0 }; assert_eq!(s, s); }",
    "fn f<T>(a: T) -> () { assert_eq!(a, a); }",
    "fn f() -> () { assert_eq!(1, (1,)); }",
    "fn f() -> () { assert_eq!([1], [1, 2]); }",
    "fn f() -> () { constrain_eq!(&0, &0); }",
    "fn f() -> () { constrain_eq!((1, &0), (1, &0)); }",
    "fn f() -> () { constrain_eq!(1, (1,)); }"
  ] do
    match Generic.Frontend.ofString env text with
    | .error _ => pure ()
    | .ok _ => throwError "unexpectedly accepted: {text}"

instance : Fact (Nat.Prime 7) := ⟨by decide⟩

def checkRows : Except String Unit := do
  let s ← Generic.prepare (source.toField Rat)
  let q ← Generic.specialize s ["arrays"]
  let c ← q.compile
  let some chip := c.system.findChip? "arrays" | throw "missing assertion chip"
  if chip.numVars != 4 then throw "array equality added auxiliary columns"
  let type : Aiur.Ty := .tuple [.field, .field]
  let left : WireValue Rat := ⟨type, [2, 3]⟩
  let unit : WireValue Rat := ⟨.tuple [], []⟩
  let row : Circuit.Row Rat := ⟨"arrays", [2, 3, 2, 3]⟩
  c.check {} ⟨"arrays", [left, left], unit⟩ [row]
  c.checkMemo {} ⟨"arrays", [left, left], unit⟩ [⟨row, 1⟩]
  for words in [[3, 3], [2, 4]] do
    let right : WireValue Rat := ⟨type, words⟩
    let bad : Circuit.Row Rat := ⟨"arrays", [2, 3] ++ words⟩
    if (c.check {} ⟨"arrays", [left, right], unit⟩ [bad]).isOk then throw "unequal values accepted"
    if (c.checkMemo {} ⟨"arrays", [left, right], unit⟩ [⟨bad, 1⟩]).isOk then throw "unequal memoized values accepted"
  let q ← Generic.specialize s ["constrained_arrays"]
  let c ← q.compile
  let some constrained := c.system.findChip? "constrained_arrays" | throw "missing constrained equality chip"
  if constrained.numVars != chip.numVars || constrained.constraints != chip.constraints then
    throw "runtime flag changed equality constraints"
  for words in [[3, 3], [2, 4]] do
    let right : WireValue Rat := ⟨type, words⟩
    let bad : Circuit.Row Rat := ⟨"constrained_arrays", [2, 3] ++ words⟩
    if (c.check {} ⟨"constrained_arrays", [left, right], unit⟩ [bad]).isOk then
      throw "deferred equality accepted an unequal circuit row"

#guard checkRows == .ok ()

def run : IO Unit := do
  let .ok s := Generic.prepare (source.toField Rat) | throw (IO.userError "assertion source failed to check")
  for (name, args, expected) in checks do
    let actual := s.run name args
    unless actual == expected do throw (IO.userError s!"{name}: {repr actual}")
    unless (s.runTraced name args).result == expected do throw (IO.userError s!"traced {name}")
    let .ok specialized := Generic.specialize s [name] | throw (IO.userError s!"specializing {name}")
    unless specialized.coreRun name args == expected do throw (IO.userError s!"lowered {name}")
    let .ok _ := specialized.compile | throw (IO.userError s!"compiling {name}")
  let traced := s.runTraced "nested_failure" []
  unless traced.result == failed (some "fields differ") &&
      traced.events.contains (.message "before assertion" [1]) &&
      traced.activeCalls == ["fields", "nested_failure"] do
    throw (IO.userError s!"assertion diagnostics: {repr traced}")
  let .ok small := Generic.prepare (source.toField (ZMod 7)) | throw (IO.userError "field conversion")
  unless (small.run "reduced" []).isOk do throw (IO.userError "equality used natural literals instead of field values")
  if let .error error := checkRows then throw (IO.userError error)
  IO.println s!"Passed {checks.length * 3} assertion execution checks and {checks.length} compilations."

end AiurAssertionTests
