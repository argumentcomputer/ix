import Aiur.Modules
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Field.ZMod

namespace AiurModuleTests
open Aiur
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000

def arithmetic : Modules.Program Nat := aiur_modules% "
signature Number {
  type T;
  const ZERO: T;
  fn make(n: Field) -> T;
  fn read(n: T) -> Field;
}
module Algorithm<N: Number> {
  fn run(n: Field) -> Field { N::read(N::make(n)) + N::read(N::ZERO) }
  fn identity<T>(x: T) -> T { x }
}
module Pair: Number {
  type T = (Field, Field);
  const ZERO: T = (0, 0);
  fn make(n: Field) -> T { (n, 7) }
  fn read(n: T) -> Field { n.0 }
  fn secret() -> Field { 99 }
}
module Alias: Number = Pair;
module App = Algorithm::<Pair>;
module Main {
  fn run(n: Field) -> Field {
    App::run(n) + Algorithm::<Alias>::run(n) + Pair::read(Alias::make(n))
  }
}
"

def features : Modules.Program Nat := aiur% "
module Data {
  enum Option<T> { None, Some(T) }
  struct Pair<T> { left: T, right: T }
  type Words = [Field; 2];
  const zero = 0;
  const unit = Option::<Field>::None;
  const cell = &(1, 2);
  fn identity<T>(x: T) -> T { x }
  fn make<T>(x: T) -> Pair<T> { Pair { left: x, right: x } }
}
module Main {
  fn run(x: Field) -> Field {
    let p = Data::make(x);
    let q = p with { .right = 2 };
    let Data::Pair { left: a, right: b } = q;
    let v = Data::Option::<Field>::Some(a);
    let Data::Option::Some(n) = v;
    let &(_, c) = Data::cell;
    let Data::zero = 0;
    let words: Data::Words = [n, b];
    Data::identity::<Field>(words[0] + words[1] + c)
  }
  fn empty() -> Data::Option<Field> { Data::unit }
  fn lower(n: Field) -> Field { match n { Data::zero => 4, _ => 8 } }
  fn f(n: Field) -> Field { n + 1 }
  fn shadow(n: Field) -> Field { let f = 90; ::f(n) + f }
}
"

def tables : Modules.Program Nat := aiur_modules% "
signature Operation { fn apply(a: Field, b: Field) -> Field; }
signature Inputs { table pairs: (Field, Field); }
module Shared: Inputs {
  table pairs: (Field, Field) { (1, 2), (2, 3) }
  table hidden: Field { 91, 92 }
}
module Addition: Operation {
  table sums: Field { 3, 5 }
  map apply(a: Field, b: Field) -> Field = Shared::pairs => sums;
}
module Product: Operation {
  table products: Field { 2, 6 }
  map apply(a: Field, b: Field) -> Field = Shared::pairs => products;
}
module Local {
  table inputs: (Field,) { (0,), (1,) }
  table outputs: Field { 10, 11 }
  map lookup(x: Field) -> Field = inputs => outputs;
  fn run(x: Field) -> Field { lookup(x) }
}
module Use<A: Operation, B: Operation> {
  fn run(a: Field, b: Field) -> (Field, Field) { (A::apply(a,b), B::apply(a,b)) }
}
module App = Use::<Addition, Product>;
"

def applications : Modules.Program Nat := aiur_modules% "
signature Op { fn run(x: Field) -> Field; }
module Base { fn run(x: Field) -> Field { x + 1 } }
module Wrap<X: Op> { fn run(x: Field) -> Field { X::run(x) + 1 } }
module Alias<X: Op> = Wrap::<X>;
module Odd { fn run(n: Field) -> Field { match n { 0 => 0, _ => Even::run(n - 1) } } }
module Even { fn run(n: Field) -> Field { match n { 0 => 1, _ => Odd::run(n - 1) } } }
module Main {
  fn nested(x: Field) -> Field { Wrap::<Alias::<Base>>::run(x) }
  fn parity(x: Field) -> Field { Even::run(x) }
}
"

def genericInterfaces : Modules.Program Nat := aiur_modules% "
signature Boxes {
  type Box<T>;
  const P: &Field;
  fn make<T>(x: T) -> Box<T>;
  fn read<T>(x: Box<T>) -> T;
}
module BoxImpl: Boxes {
  struct Box<T> { value: T }
  const P = &7;
  fn make<T>(x: T) -> Box<T> { Box { value: x } }
  fn read<T>(x: Box<T>) -> T { x.value }
}
module Algorithm<X: Boxes> {
  struct Envelope<T> { value: T }
  enum Packet<T> { Value(T) }
  fn run() -> Field {
    let &n = X::P;
    let v = Envelope::<X::Box<Field>> { value: X::make(n) };
    let Envelope::<X::Box<Field>> { value: x } = v;
    let p = Packet::<X::Box<Field>>::Value(x);
    let Packet::<X::Box<Field>>::Value(x) = p;
    X::read(x)
  }
}
"

def execute (p : Modules.Program Nat) (entry : String) (args : List (SourceValue Rat)) := do
  let p ← Modules.prepare (p.toField Rat) [entry]
  p.run entry args

def templates : Modules.Program Nat := aiur_modules% "
module Options {
  enum Maybe<T> { None, Some(T) }
  const empty = Maybe::None;
}
module Alias = Options;
module Main {
  fn scalar() -> Options::Maybe<Field> { Alias::empty }
  fn pair() -> Options::Maybe<(Field,Field)> { Options::empty }
  fn run() -> Field {
    let Options::Maybe::None = scalar();
    let Options::Maybe::None = pair();
    7
  }
}
"

def cases : List (String × Except String (SourceValue Rat × Heap Rat) × SourceValue Rat) := [
  ("abstract functor", execute arithmetic "App::run" [.field 9], .field 9),
  ("alias identities", execute arithmetic "Main::run" [.field 4], .field 12),
  ("direct application", execute arithmetic "Algorithm::<Pair>::run" [.field 7], .field 7),
  ("qualified aggregates and consts", execute features "Main::run" [.field 5], .field 9),
  ("const arm", execute features "Main::lower" [.field 0], .field 4),
  ("fallback arm", execute features "Main::lower" [.field 3], .field 8),
  ("rooted callable bypasses local", execute features "Main::shadow" [.field 3], .field 94),
  ("shared input tables", execute tables "App::run" [.field 2,.field 3], .tuple [.field 5,.field 6]),
  ("unqualified table references", execute tables "Local::run" [.field 1], .field 11),
  ("nested applications", execute applications "Main::nested" [.field 1], .field 4),
  ("mutual modules", execute applications "Main::parity" [.field 6], .field 1),
  ("generic signature members", execute genericInterfaces "Algorithm::<BoxImpl>::run" [], .field 7),
  ("contextual const templates through aliases", execute templates "Main::run" [], .field 7)
]

run_cmd do
  let env ← Lean.getEnv
  -- Fragments may refer to declarations supplied by another metaprogram.
  let get {α : Type} (result : Except String α) : Lean.Elab.Command.CommandElabM α :=
    match result with
    | .ok value => pure value
    | .error error => throwError "{error}"
  let left ← get <| Modules.Frontend.parse env
    "module Client { fn run() -> Field { Provider::value() + Adapter::<Provider>::value() } }"
  let right ← get <| Modules.Frontend.parse env
    "signature S { fn value() -> Field; } module Provider { fn value() -> Field { 8 } } module Adapter<X: S> { fn value() -> Field { X::value() + 1 } }"
  let combined := left.append right
  let _ ← get <| Modules.checkTemplates combined
  let (value,_) ← get <| execute combined "Client::run" []
  unless value == .field 17 do throwError "composed module execution returned {repr value}"
  unless (Modules.checkTemplates (combined.append right)).toOption.isNone do
    throwError "composition silently reopened a module"
  let rejected : List (String × String) := [
    ("fn root() -> Field { 0 }", "expected"),
    ("type Root = Field;", "expected"),
    ("const ROOT = 0;", "expected"),
    ("module A { module B {} }", "expected"),
    ("signature A { signature B {} }", "expected"),
    ("module A {} signature A {}", "duplicate"),
    ("module A {} module A {}", "duplicate"),
    ("module A { type x = Field; const x = 0; }", "duplicate"),
    ("module A: Missing {}", "unknown signature"),
    ("module A = B; module B = A;", "depth"),
    ("signature S { fn f() -> Field; } module M: S { fn f() -> Field { 1 } fn hidden() -> Field { 2 } } module A { fn run() -> Field { M::hidden() } }", "not exposed"),
    ("signature S { type T; fn make() -> T; } module M: S { type T = Field; fn make() -> T { 1 } } module A { fn run() -> Field { M::make() + 1 } }", "type mismatch"),
    ("signature S { type T; fn make() -> T; } module M: S { struct T { x: Field } fn make() -> T { T { x: 1 } } } module A { fn run() -> Field { M::make().x } }", "requires a struct"),
    ("signature S { type T; } module M: S { enum T { A } } module A { fn run() -> M::T { M::T::A } }", "not exposed"),
    ("signature S { type T; const C: T; } module M: S { type T = Field; const C = 7; } module Proxy { const C = M::C; } module A { fn run() -> Field { Proxy::C + 1 } }", "type mismatch"),
    ("signature S { type T; fn make() -> T; } module Bad<X: S> { fn run() -> Field { X::make() + 1 } }", "type mismatch"),
    ("signature S { fn f() -> Field; } module Bad<X: S> { fn run() -> Field { X::missing() } }", "not exposed"),
    ("signature S { fn f() -> Field; } module M: S { fn f() -> () { () } }", "does not satisfy"),
    ("signature S { const C: Field; } module M: S {}", "missing const"),
    ("signature S { type T = Field; } module M: S { type T = (Field,Field); }", "manifest type mismatch"),
    ("signature S { type T; } signature Concrete { type T = Field; } module M: S { type T = Field; } module F<X: Concrete> {} module Bad = F::<M>;", "manifest type mismatch"),
    ("signature S { fn f() -> Field; } module M: S { fn f() -> Field { 1 } fn hidden() -> Field { 2 } } signature Big { fn f() -> Field; fn hidden() -> Field; } module F<X: Big> {} module Bad = F::<M>;", "missing or incompatible callable"),
    ("module M { fn f() -> Field { 1 } fn main() -> Field { let f = 0; f() } }", "not callable"),
    ("module M { type A = B; type B = A; }", "cyclic type alias"),
    ("module A { const X = B::X; } module B { const X = A::X; }", "const"),
    ("signature S { opaque type T; fn make() -> T; } module F<X: S> { fn run() -> () { assert_eq!(X::make(), X::make()); } }", "pointer"),
    ("signature S { opaque type T; } module F<X: S> { fn run() -> X::T { hint::<X::T>(()) } }", "non-opaque"),
    ("signature S { type T; } module F<X: S> { type Alias = X::T; fn run() -> X::T { Alias::«opaque»(&0) } }", "constructor"),
    ("signature S { type T; } module F<X: S> { type Alias = X::T; fn run() -> X::T { Alias::«@opaque»(&0) } }", "unexpected '@'"),
    ("signature S {} module M {} module F<M: S> {}", "shadows"),
    ("module M { fn grow<T>(x: T) -> T { grow((x,x)).0 } }", "changes type arguments"),
    ("module A { fn f<T>(x: T) -> T { B::g((x,x)).0 } } module B { fn g<T>(x: T) -> T { A::f(x) } }", "changes type arguments")
  ]
  for (source, message) in rejected do
    match Modules.Frontend.ofString env source with
    | .ok _ => throwError "accepted invalid module source: {source}"
    | .error error =>
        unless (error.splitOn message).length > 1 do
          throwError "expected '{message}', got '{error}' for: {source}"

#print axioms Modules.Prepared.run_spec
#print axioms Modules.Prepared.run_heap_spec
#print axioms Modules.Assembly.function_origin
#print axioms Modules.Compiled.check_complete
#print axioms Modules.Compiled.checkMemo_complete
#print axioms Modules.Compiled.run_complete
#print axioms Modules.Compiled.runMemo_complete
#print axioms Modules.Compiled.check_sound
#print axioms Modules.Compiled.checkerMemo_acyclic_sound
#print axioms Modules.Compiled.checkMemo_acyclic_sound

def run : IO Unit := do
  for (label, actual, expected) in cases do
    match actual with
    | .ok (value, _) => unless value == expected do throw (IO.userError s!"{label}: {repr value}")
    | .error e => throw (IO.userError s!"{label}: {e}")
  for (p,entries) in [(arithmetic,["App::run","Algorithm::<Pair>::run","Algorithm::<Alias>::run"]),
      (features,["Main::run","Main::lower","Main::shadow"]), (tables,["App::run","Local::run"]),
      (applications,["Main::nested","Main::parity"]), (genericInterfaces,["Algorithm::<BoxImpl>::run"]),
      (templates,["Main::run"])] do
    let .ok prepared := Modules.prepare (p.toField Rat) entries | throw (IO.userError "module preparation failed")
    let .ok compiled := prepared.compile | throw (IO.userError "module circuit compilation failed")
    unless compiled.circuit.system.chips.length > 0 do throw (IO.userError "no compiled modules")
  let .ok prepared := Modules.prepare (arithmetic.toField Rat)
    ["App::run","Algorithm::<Pair>::run","Algorithm::<Alias>::run"] | throw (IO.userError "alias preparation failed")
  unless prepared.entries.eraseDups.length == 1 do throw (IO.userError "module aliases duplicated an instance")
  unless (prepared.run "Pair::secret" []).toOption.isNone do throw (IO.userError "unselected private entry")
  unless (Modules.prepare (arithmetic.toField Rat) ["Pair::secret"]).toOption.isNone do throw (IO.userError "private entry accepted")
  IO.println s!"Passed {cases.length} module execution checks, module rejections, shared-instance checks, and 6 compilations."

end AiurModuleTests
