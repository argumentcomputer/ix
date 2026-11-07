import Aiur.Generic
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Field.ZMod

namespace AiurConstTests
open Aiur
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
instance : Fact (Nat.Prime 101) := ⟨by decide⟩

def source : Generic.Program Nat := aiur% "
const ptr = &(::zero,);
const zero = 0;
const Pair = (one, ::one);
const one = 1;
const aliasOne = one;
const unit = ();
const empty = Maybe::None;
const fixed = Maybe::<Field>::None;
const somePtr = Maybe::Some(::ptr);
const nested = &Maybe::Some((Pair, ptr));
type Maybe<T> = Option<T>;
enum Option<T> { None, Some(T) }

fn scalar() -> Field { zero + ::one }
fn shadow(zero: Field) -> Field { let one = zero; one + ::one }
fn before_binding() -> Field { let one = one + 1; one }
fn closed_template(one: Field) -> Field { aliasOne }
fn upper() -> Field { match 7 { Pair => Pair } }
fn lower(x: Field) -> Field { match x { ::zero => 17, zero => zero } }
fn branch_scope(x: Field) -> Field { match x { 0 => { let one = 9; one }, one => one + ::one } }
fn make() -> &(Field,) { ::ptr }
fn repeated() -> (&(Field,), &(Field,)) { (::ptr, ptr) }
fn inspect(p: &(Field,)) -> Field { match p { ::ptr => 7, _ => 9 } }
fn main(x: Field) -> Field { inspect(&(x,)) }
fn let_match(x: Field) -> Field { let ::ptr = &(x,); 11 }
fn deep() -> Field { let ::nested = nested; 13 }
fn inferred() -> Option<(Field, Field)> { empty }
fn explicit() -> Option<Field> { fixed }
fn enum_match() -> Field { match somePtr { ::somePtr => 23, _ => 29 } }
fn nullary(::unit: ()) -> Field { 31 }
fn call_unit() -> Field { nullary(unit) }
fn lazy() -> Field { match 0 { 0 => 37, _ => { let ::ptr = &(1,); 1 / 0 } } }
fn generic<T>(x: Option<T>) -> Field { match x { ::empty => 41, _ => 43 } }
fn generic_entry() -> Field { generic(Option::<Field>::None) }
"

#guard source.consts.length == 10
#guard source.aliases.length == 1
#guard (source.findFunction? "make").map (·.body) == some (.global "ptr" (some (.ptr (.tuple [.field]))))

def runSource (name : String) (args : List (SourceValue Rat) := []) := do
  let s ← Generic.prepare (source.toField Rat)
  s.run name args

def runSpecialized (name : String) (args : List (SourceValue Rat) := []) := do
  let s ← Generic.prepare (source.toField Rat)
  let q ← Generic.specialize s [name]
  q.run name args

#guard runSource "scalar" == .ok (.field 1, [])
#guard runSource "shadow" [.field 5] == .ok (.field 6, [])
#guard runSource "before_binding" == .ok (.field 2, [])
#guard runSource "closed_template" [.field 99] == .ok (.field 1, [])
#guard runSource "upper" == .ok (.field 7, [])
#guard runSource "lower" [.field 0] == .ok (.field 17, [])
#guard runSource "lower" [.field 3] == .ok (.field 3, [])
#guard runSource "branch_scope" [.field 0] == .ok (.field 9, [])
#guard runSource "branch_scope" [.field 4] == .ok (.field 5, [])
#guard runSource "repeated" == .ok
  (.tuple [.ptr (.tuple [.field]) 0, .ptr (.tuple [.field]) 1], [.tuple [.field 0], .tuple [.field 0]])
#guard runSpecialized "main" [.field 0] == .ok (.field 7, [.tuple [.field 0]])
#guard runSpecialized "main" [.field 1] == .ok (.field 9, [.tuple [.field 1]])
#guard runSource "let_match" [.field 0] == .ok (.field 11, [.tuple [.field 0]])
#guard runSource "let_match" [.field 1] == .error (reprStr EvalError.patternMismatch)
#guard (runSpecialized "deep").map Prod.fst == .ok (.field 13)
#guard runSpecialized "inferred" == runSource "inferred"
#guard (runSpecialized "enum_match").map Prod.fst == .ok (.field 23)
#guard runSource "call_unit" == .ok (.field 31, [])
#guard runSource "lazy" == .ok (.field 37, [])
#guard runSource "generic_entry" == .ok (.field 41, [])

#guard (do
  let s ← Generic.prepare (source.toField (ZMod 101))
  let q ← Generic.specialize s ["main", "repeated", "deep", "enum_match", "lazy", "generic_entry", "let_match"]
  return (← q.compile).system.chips.length).toOption.isSome

def tables : Generic.Program Nat := aiur% "
const a = 1;
const b = 2;
const Key = (::a, ::b);
table keys: (Field, Field) { ::Key }
table outputs: Field { b }
map lookup(x: Field, y: Field) -> Field = keys => outputs;
fn main() -> Field { lookup(a, b) }
"
#guard (do
  let s ← Generic.prepare (tables.toField Rat)
  let q ← Generic.specialize s ["main"]
  q.run "main" []) == .ok (.field 2, [])

def fieldCollision : Generic.Program Nat := aiur% "
const a = &1;
const b = &102;
fn test(p: &Field) -> Field { match p { ::a => 1, ::b => 2, _ => 3 } }
"
#guard (Generic.prepare (fieldCollision.toField (ZMod 101))).toOption.isNone

def literalCollision : Generic.Program Nat := aiur% "
const a = 1;
const b = 102;
fn main(x: Field) -> Field { match x { ::a => 7, ::b => 8, _ => 9 } }
"
#guard (do
  let s ← Generic.prepare (literalCollision.toField (ZMod 101))
  let q ← Generic.specialize s ["main"]
  return (← q.compile).system.chips.length).toOption.isNone

def tableCollision : Generic.Program Nat := aiur% "
const a = 1;
const b = 102;
table inputs: (Field,) { (a,), (b,) }
table outputs: Field { 0, 1 }
map lookup(x: Field) -> Field = inputs => outputs;
"
#guard (Generic.prepare (tableCollision.toField (ZMod 101))).toOption.isNone

def handBuilt : Generic.Program Nat := {
  consts := [⟨"zero", .literal 0⟩, ⟨"cell", .load (.global "zero")⟩]
  functions := [{
    name := "main", params := [], result := .field
    body := .letValue (.global "cell") (.global "cell") (.literal 7)
  }]
}
#guard (do
  let s ← Generic.prepare (handBuilt.toField Rat)
  s.run "main" []) == .ok (.field 7, [.field 0])
#guard (Generic.prepare (({ handBuilt with consts := [⟨"bad", .bind "x"⟩] }).toField Rat)).toOption.isNone
#guard (Generic.prepare (({ handBuilt with consts := [⟨"bad", .wildcard⟩] }).toField Rat)).toOption.isNone

run_cmd do
  for code in [
    "const A = ::A;",
    "const a = b; const b = &a;",
    "const a = ::b; const b = &::a;",
    "const a = (0, ::b); const b = (1, ::c); const c = ::a;",
    "const a = ::unknown;",
    "const a = 0; const a = 1;",
    "const a = x;",
    "const a = _;",
    "const a = &(0, _);",
    "const a = 1 + 2;",
    "const a = *(&0);",
    "const a = hint::<Field>(0);",
    "const a = Missing::A;",
    "enum E { A } const a = E::B;",
    "enum E { A(Field) } const a = E::A;",
    "enum E { A(Field) } const a = E::A(());",
    "enum E<T> { A(T, T) } const a = E::A(0, ());",
    "enum E<T> { A } const a = E::<Missing>::A;",
    "const a = 0; fn a() -> Field { 0 }",
    "const a = 0; table keys: () {} table outputs: Field {} map a() -> Field = keys => outputs;",
    "fn main() -> Field { ::missing }",
    "fn main(missing: Field) -> Field { ::missing }",
    "fn main(x: Field) -> Field { match x { ::missing => 0, _ => 1 } }",
    "const a = &0; fn f(x: Field) -> Field { let ::a = x; 0 }",
    "const a = 0; fn f(::a: Field) -> Field { 1 }",
    "const a = &0; table cells: &Field { a }"
  ] do
    match Generic.Frontend.ofString (← Lean.getEnv) code with
    | .error _ => pure ()
    | .ok _ => throwError "unexpectedly accepted: {code}"
  match Frontend.ofString (← Lean.getEnv) "const a = 0; fn main() -> Field { 0 }" with
  | .error _ => pure ()
  | .ok _ => throwError "legacy frontend discarded a const declaration"

def run : IO Unit := do
  let checks := [
    ("const expression", runSource "scalar", .ok (.field 1, [])),
    ("const shadowing", runSource "shadow" [.field 5], .ok (.field 6, [])),
    ("const pointer match", runSpecialized "main" [.field 0], .ok (.field 7, [.tuple [.field 0]])),
    ("const pointer fallback", runSpecialized "main" [.field 1], .ok (.field 9, [.tuple [.field 1]])),
    ("const refutable let", runSource "let_match" [.field 1], .error (reprStr EvalError.patternMismatch)),
    ("const inactive body", runSource "lazy", .ok (.field 37, []))
  ]
  for (name, actual, expected) in checks do
    unless actual = expected do throw (IO.userError s!"{name}: expected {repr expected}, got {repr actual}")
  IO.println s!"Passed {checks.length} const execution checks."

example (p : Generic.Program Nat) (F : Type) [NatCast F] :
    Generic.expandConsts (p.toField F) = (Generic.expandConsts p).map (fun q => q.toField F) :=
  Generic.expandConsts_toField p F

/-- info: 'Aiur.Generic.expandConsts_toField' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Generic.expandConsts_toField

end AiurConstTests
