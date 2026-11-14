import Aiur.Modules
import Aiur.Optimized.NativeCorrectness
import Mathlib.Algebra.Field.Rat

namespace AiurOpacityTests
open Aiur
set_option maxRecDepth 20000
set_option maxHeartbeats 12000000

def source : Modules.Program Nat := aiur% "
signature Open { type Byte; fn read(x: Byte) -> Field; }
signature Closed {
  opaque type Byte;
  fn make(x: Field) -> Byte;
  fn read(x: Byte) -> Field;
}
module Bytes {
  opaque type Byte = Field;
  type Alias = Byte;
  opaque type Pair<T> = (T, T);
  opaque struct Secret { value: Field }
  opaque enum Choice { Empty, Some(Field) }
  const ZERO: Byte = 0;
  table inputs: (Field, Field) { (0, 0), (0, 1), (1, 0), (1, 1) }
  table outputs: Byte { 0, 1, 1, 0 }
  map raw_xor(a: Field, b: Field) -> Byte = inputs => outputs;
  inline fn xor(a: Byte, b: Byte) -> Byte { raw_xor(a, b) }
  fn make(x: Field) -> Byte { let 0 = x * (x - 1); x }
  inline fn read(x: Byte) -> Field { x }
  fn pair<T>(x: T, y: T) -> Pair<T> { (x, y) }
  fn first<T>(p: Pair<T>) -> T { p.0 }
  fn secret(x: Field) -> Secret { Secret { value: x } }
  fn reveal(x: Secret) -> Field { x.value }
  fn choice(x: Field) -> Choice { Choice::Some(x) }
  fn inspect(x: Choice) -> Field { match x { Choice::Empty => 0, Choice::Some(x) => x } }
  fn input(x: Alias) -> Field { x }
  fn secret_input(x: Secret) -> Field { x.value }
  fn choice_input(x: Choice) -> Field { inspect(x) }
}
module Copy = Bytes;
module API: Closed = Bytes;
module Transparent: Open {
  type Byte = Field;
  fn read(x: Byte) -> Field { x }
  fn make(x: Field) -> Byte { x }
}
module Plain {
  type Byte = Field;
  fn make(x: Field) -> Byte { x }
  fn read(x: Byte) -> Field { x }
}
module Witness<X: Open> {
  fn run() -> Field { X::read(hint::<X::Byte>(())) }
  fn equal() -> () { let x = hint::<X::Byte>(()); assert_eq!(x, x); }
  fn input(x: X::Byte) -> Field { X::read(x) }
}
module Consumer<X: Closed> {
  fn run() -> Field { X::read(X::make(1)) }
  fn input(x: X::Byte) -> Field { X::read(x) }
}
module Main {
  struct Nested { value: [Bytes::Byte; 0] }
  enum Maybe { Empty, Some(Bytes::Byte) }
  fn raw(a: Field, b: Field) -> Field { Bytes::read(Bytes::raw_xor(a, b)) }
  fn typed() -> Field { Bytes::read(Bytes::xor(Bytes::make(1), Bytes::ZERO)) }
  fn copy(x: Copy::Byte) -> Bytes::Byte { x }
  fn aliases() -> Field { API::read(copy(Bytes::make(1))) }
  fn aggregates() -> Field {
    Bytes::first(Bytes::pair(3, 9)) + Bytes::reveal(Bytes::secret(4)) +
      Bytes::inspect(Bytes::choice(5))
  }
  fn memory() -> Field { let p = &Bytes::make(1); Bytes::read(*p) }
  fn hinted_key() -> Field { hint::<Field>(Bytes::make(1)) }
  fn nested_input(x: Nested) -> () { () }
  fn enum_input(x: Maybe) -> () { () }
  fn pointer_input(x: &Field) -> Field { *x }
}
"

run_cmd do
  let env ← Lean.getEnv
  -- Programmatically assembled declarations obey the same signature restriction.
  let type : Modules.TypeMember := { name := "T", isOpaque := true, definition := some .field }
  let malformed : Modules.Program Nat := { signatures := [{ name := "S", types := [type] }] }
  unless (Modules.validate malformed).toOption.isNone do
    throwError "accepted an opaque signature member with a manifest representation"
  let accepted : List String := [
    "signature S { opaque type Box<T>; fn make<T>(x: T) -> Box<T>; fn read<T>(x: Box<T>) -> T; } module M: S { opaque type Box<T> = (T,); fn make<T>(x: T) -> Box<T> { (x,) } fn read<T>(x: Box<T>) -> T { x.0 } } module F<X: S> { fn run() -> Field { X::read(X::make(3)) } } module A = F::<M>;",
    "signature S { opaque type Box<T>; } module M: S { type Box<T> = (T,); }",
    "signature S { type Box<T>; } module M { type Box<T> = (T,); } module F<X: S> { fn f() -> X::Box<Field> { hint::<X::Box<Field>>(()) } } module A = F::<M>;",
    "signature S { opaque type T; } module M: S { type T = Field; fn f() -> T { hint::<T>(()) } }",
    "module M { opaque enum E { A(Field) } type Alias = E; fn f(x: Field) -> Alias { Alias::A(x) } }"
  ]
  for source in accepted do
    let .ok program := Modules.Frontend.parse env source |
      throwError "opacity regression has invalid syntax: {source}"
    match Modules.checkTemplates program with
    | .ok _ => pure ()
    | .error e => throwError "rejected valid opacity operation: {source}\n{e}"
  let rejected : List String := [
    "module M { opaque type T = Field; fn f() -> T { hint::<T>(()) } }",
    "module M { opaque type T = Field; type A = T; fn f() -> A { hint::<A>(()) } }",
    "module M { opaque type T = Field; struct S { x: T } fn f() -> S { hint::<S>(()) } }",
    "module M { opaque type T = Field; enum E { None, Some(T) } fn f() -> E { hint::<E>(()) } }",
    "module M { opaque type T = Field; fn f() -> [T; 0] { hint::<[T; 0]>(()) } }",
    "module M { opaque type T = Field; fn f() -> Field { match 0 { 0 => 1, _ => { let x = hint::<T>(()); 2 } } } }",
    "module M { opaque type T = Field; fn f() -> Field { hint::<Field>(hint::<T>(() )) } }",
    "module M { opaque type T = Field; } module N { fn f() -> M::T { 0 } }",
    "module M { opaque type T = Field; } module N { fn f(x: M::T) -> Field { x + 1 } }",
    "module M { opaque type A = Field; opaque type B = Field; } module N { fn f(x: M::A) -> M::B { x } }",
    "module M { opaque type A<T> = Field; } module N { fn f(x: M::A<Field>) -> M::A<(Field, Field)> { x } }",
    "module M { opaque type T = (Field, Field); } module N { fn f(x: M::T) -> Field { x.0 } }",
    "module M { opaque type T = [Field; 2]; } module N { fn f(x: M::T) -> Field { x[0] } }",
    "module M { opaque type T = (Field, Field); } module N { fn f(x: M::T) -> Field { let (a, b) = x; a } }",
    "module M { opaque struct S { x: Field } } module N { fn f(x: M::S) -> Field { x.x } }",
    "module M { opaque struct S { x: Field } } module N { fn f() -> M::S { M::S { x: 0 } } }",
    "module M { opaque struct S { x: Field } } module N { fn f(x: M::S) -> M::S { x with { .x = 1 } } }",
    "module M { opaque enum E { A(Field) } } module N { fn f() -> M::E { M::E::A(0) } }",
    "module M { opaque enum E { A(Field) } } module N { fn f(x: M::E) -> Field { let M::E::A(v) = x; v } }",
    "module M { opaque type T = Field; type A = T; } module N { fn f() -> M::A { 0 } }",
    "module M { opaque type T = Field; } module A = M; module N { fn f() -> A::T { 0 } }",
    "module M { opaque type T = Field; } module A = M; module N { fn f() -> A::T { hint::<A::T>(()) } }",
    "module M { opaque type T = Field; const ZERO: T = 0; } module N { fn f() -> Field { M::ZERO } }",
    "signature S { type T; } module M: S { opaque type T = Field; }",
    "signature S { type T = &Field; }",
    "signature S { opaque type T; type Alias = T; }",
    "signature S { opaque type T; type Box<A> = (A, T); }",
    "signature S { type T; } module M: S { struct T { p: &Field } }",
    "signature S { type T; } module M: S { opaque type Hidden = Field; struct T { x: Hidden } }",
    "signature S { type T = Field; } module M: S { opaque type T = Field; }",
    "signature S { fn read(x: Field) -> Field; } module M: S { opaque type T = Field; fn read(x: T) -> Field { x } }",
    "signature S { fn make() -> Field; } module M: S { opaque type T = Field; fn make() -> T { 0 } }",
    "signature S { const C: Field; } module M: S { opaque type T = Field; const C: T = 0; }",
    "signature S { type T; } module M { opaque type T = Field; } module F<X: S> {} module A = F::<M>;",
    "signature S { type T; } signature O { opaque type T; } module M: O { type T = Field; } module F<X: S> {} module A = F::<M>;",
    "signature S { opaque type T; } module M { type T = Field; } module F<X: S> { fn f() -> X::T { hint::<X::T>(()) } } module A = F::<M>;",
    "signature S { opaque type T; } module F<X: S> { fn f() -> [X::T; 0] { hint::<[X::T; 0]>(()) } }",
    "signature S { type Box<T>; } module M: S { opaque type Box<T> = (T,); }",
    "signature S { type Box<T>; } module M: S { type Box<T> = &T; }",
    "signature S { opaque type Box<T>; } module F<X: S> { fn f() -> X::Box<Field> { hint::<X::Box<Field>>(()) } }",
    "signature O { type T; } signature S { opaque type T; } module M { type T = Field; } module F<X: O, Y: S> { fn f() -> Y::T { hint::<Y::T>(()) } } module A = F::<M, M>;",
    "module M { opaque type A = B; type B = A; }",
    "module M { opaque type A = N::B; } module N { opaque type B = M::A; }",
    "module M { opaque type T = N::Alias; } module A = M; module N { type Alias = A::T; }",
    "module M { opaque type T = &Field; table rows: T {} }"
  ]
  for source in rejected do
    let .ok program := Modules.Frontend.parse env source |
      throwError "opacity regression has invalid syntax: {source}"
    match Modules.checkTemplates program with
    | .ok _ => throwError "accepted forbidden opacity operation: {source}"
    | .error _ => pure ()

private def get {α : Type} : Except String α → IO α
  | .ok x => pure x
  | .error e => throw (IO.userError e)

def run : IO Unit := do
  let cases : List (String × List (SourceValue Rat) × SourceValue Rat) := [
    ("Main::raw", [1, 0], 1), ("Main::raw", [1, 1], 0),
    ("Main::typed", [], 1), ("Main::aliases", [], 1),
    ("Main::aggregates", [], 12), ("Main::memory", [], 1),
    ("Main::hinted_key", [], 7), ("Witness::<Transparent>::run", [], 7),
    ("Witness::<Transparent>::equal", [], .tuple []),
    ("Witness::<Transparent>::input", [8], 8),
    ("Consumer::<Bytes>::run", [], 1), ("Consumer::<Plain>::run", [], 1)
  ]
  let prepared ← get <| Modules.prepare (source.toField Rat) ((cases.map (·.1)).eraseDups)
  let hints := prepared.environment.source.checkedHints fun _ _ => .ok (.field 7)
  let compiled ← get prepared.compile
  let optimized ← get prepared.compileOptimized
  for (name, args, expected) in cases do
    let (actual, _) ← get <| prepared.run name args (fuel := 10000) (hints := hints)
    unless actual == expected do throw (IO.userError s!"opaque source execution: {name}")
    let some entry := prepared.find? name | throw (IO.userError "missing selected entry")
    let coreHints := HintProvider.checked compiled.circuit.program.enums fun _ _ => .ok (.field 7)
    let (after, _) ← get <| (Aiur.run compiled.circuit.program entry.resolved.name args
      10000 coreHints).mapError reprStr
    unless after == expected do throw (IO.userError s!"opaque compiled execution: {name}")
  unless (prepared.run "Main::raw" [2, 0]).toOption.isNone do
    throw (IO.userError "raw opaque map accepted a missing input")
  for name in ["Bytes::input", "Copy::input", "Bytes::secret_input", "Bytes::choice_input",
      "Main::copy", "Main::nested_input", "Main::enum_input", "Main::pointer_input",
      "Consumer::<Bytes>::input", "Consumer::<Plain>::input"] do
    unless (Modules.prepare (source.toField Rat) [name]).toOption.isNone do
      throw (IO.userError s!"opaque entry accepted: {name}")
  let some raw := optimized.circuit.system.findChip? "Main::raw" |
    throw (IO.userError "missing raw map entry")
  unless raw.numVars == 3 && raw.sends.length == 1 do
    throw (IO.userError "opaque alias added representation columns or lookups")
  for (a, b, result) in [(0, 0, 0), (0, 1, 1), (1, 0, 1), (1, 1, 0)] do
    let row : Circuit.Row Rat := ⟨"Main::raw", [a, b, result]⟩
    let root : Circuit.Message Rat := ⟨"Main::raw", [.field a, .field b], .field result⟩
    let _ ← get <| optimized.check ⟨[]⟩ root.channel root.args root.result [row]
    let _ ← get <| optimized.checkMemo ⟨[]⟩ root.channel root.args root.result [⟨row, 1⟩]
    unless (optimized.check ⟨[]⟩ root.channel root.args (.field (result + 1)) [row]).toOption.isNone do
      throw (IO.userError "wrong opaque map output accepted")
  IO.println s!"Passed {cases.length} opacity execution checks, signature/entry rejections, and opaque map rows in both checkers."

#print axioms Modules.nonOpaque_declared
#print axioms Modules.Compiled.check_complete
#print axioms Modules.Compiled.check_sound
#print axioms Modules.Compiled.checkMemo_acyclic_sound
#print axioms Optimized.ModulesArtifact.check_complete
#print axioms Optimized.ModulesArtifact.check_sound

end AiurOpacityTests
