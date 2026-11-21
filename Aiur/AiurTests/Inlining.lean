import Aiur.Modules
import Mathlib.Algebra.Field.Rat

namespace AiurInlineTests
open Aiur
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000

def source : Modules.Program Nat := aiur% "
signature Operation { fn next(x: Field) -> Field; }
module Helpers: Operation {
  inline fn next(x: Field) -> Field { return x + 1; }
}
module Alias: Operation = Helpers;
module Use<X: Operation> {
  fn run(x: Field) -> Field { X::next(x) + 1 }
}
module Main {
  enum Maybe<T> { Empty, Some(T) }
  struct Pair { left: Field, right: Field }
  inline fn identity<T>(x: T) -> T { x }
  inline fn shifted(x: Field) -> Field { identity(x) + Helpers::next(x) }
  inline fn unit() -> () { () }
  inline fn pair(x: Field, y: Field) -> Field { let z = x * 10; z + y }
  inline fn copy(p: &Field) -> (Field, Field) { (*p, *p) }
  inline fn choose(x: Field) -> Field {
    'block: { match x { 0 => return 7, _ => break 'block 8 }; }
  }
  inline fn step(n: Field) -> Field { recur(n - 1) + 1 }
  inline fn witness(key: Field) -> Field { hint::<Field>(key) }
  inline fn unused(_x: Field) -> Field { 3 }
  inline fn take((x, y): (Field, Field)) -> Field { x + y }
  fn nested(x: Field) -> Field { shifted(x) }
  fn zero_args() -> Field { unit(); 5 }
  fn shadow(x: Field) -> Field { let y = 3; let z = 100; pair(y, x) + z }
  fn once(x: Field) -> (Field, Field) { copy(&x) }
  fn order() -> Field { pair(*&1, *&2) }
  fn returns(x: Field) -> Field { choose(x) + 1 }
  fn recur(n: Field) -> Field { match n { 0 => 0, _ => step(n) } }
  fn aggregates() -> Field {
    let Maybe::Some(a) = identity(Maybe::Some([2, 3]));
    let Pair { left: x, right: y } = identity(Pair { left: a[0], right: a[1] });
    take(identity((x, y)))
  }
  fn hints(x: Field) -> Field { pair(witness(*&x), witness(*&(x + 1))) }
  fn failed_arg() -> Field { unused(1 / 0) }
  fn inactive(x: Field) -> Field { match x { 0 => 9, _ => witness(x) } }
  fn through_alias(x: Field) -> Field { Alias::next(x) }
}
"

def provider : HintDispatcher Rat := fun _ key =>
  match key with
  | .field x => .ok (.field (x + 1))
  | _ => .error .unavailable

abbrev Result := Except String (SourceValue Rat × Heap Rat)
def cases : List (String × List (SourceValue Rat) × Result) := [
  ("Main::nested",[3],.ok (7,[])),
  ("Main::zero_args",[],.ok (5,[])),
  ("Main::shadow",[5],.ok (135,[])),
  ("Main::once",[6],.ok (.tuple [6,6],[6])),
  ("Main::order",[],.ok (12,[1,2])),
  ("Main::returns",[0],.ok (8,[])),
  ("Main::returns",[1],.ok (9,[])),
  ("Main::recur",[5],.ok (5,[])),
  ("Main::aggregates",[],.ok (5,[])),
  ("Main::hints",[2],.ok (34,[2,3])),
  ("Main::inactive",[0],.ok (9,[])),
  ("Main::through_alias",[5],.ok (6,[])),
  ("Use::<Alias>::run",[5],.ok (7,[]))
]

run_cmd do
  let env ← Lean.getEnv
  let invalid := [
    "module M { inline fn f() -> Field { f() } }",
    "module M { inline fn f<T>(x: T) -> T { f(x) } }",
    "signature S { fn f() -> Field; } module Loop<X: S> { inline fn g() -> Field { X::f() } } module A { inline fn f() -> Field { Loop::<A>::g() } }",
    "module M { inline fn f() -> Field { g() } inline fn g() -> Field { f() } }",
    "module A { inline fn f() -> Field { B::g() } } module B { inline fn g() -> Field { A::f() } }",
    "module A { inline fn f() -> Field { Alias::g() } } module B { inline fn g() -> Field { A::f() } } module Alias = B;",
    "signature S { fn g() -> Field; } module A { inline fn f() -> Field { Alias::g() } } module B: S { inline fn g() -> Field { A::f() } } module Alias: S = B;",
    "signature S {} module M<X: S> { inline fn f() -> Field { f() } }"
  ]
  for text in invalid do
    match Modules.Frontend.ofString env text with
    | .ok _ => throwError "accepted inline cycle: {text}"
    | .error e => unless (e.splitOn "inline cycle").length > 1 do
        throwError "expected an inline-cycle diagnostic, got: {e}"
  match Modules.Frontend.ofString env "module M { inline inline fn f() -> Field { 0 } }" with
  | .ok _ => throwError "accepted repeated modifier"
  | .error _ => pure ()

#print axioms Inlining.Prepared.entry_iff
#print axioms Generic.Compiled.native_entry_iff
#print axioms Generic.Compiled.heap_complete
#print axioms Generic.Compiled.heap_sound
#print axioms Modules.Compiled.check_complete
#print axioms Modules.Compiled.checkMemo_complete
#print axioms Modules.Compiled.check_sound
#print axioms Modules.Compiled.checkMemo_acyclic_sound

def run : IO Unit := do
  let get {α : Type} (r : Except String α) : IO α := match r with
    | .ok value => pure value
    | .error e => throw (IO.userError e)
  let entries := (cases.map (·.1)).eraseDups ++ ["Main::failed_arg"]
  let p ← get <| Modules.prepare (source.toField Rat) entries
  let compiled ← get p.compile
  let core := compiled.circuit.program
  let inlineNames := compiled.specialized.inlineNames
  unless inlineNames.length ≥ 10 do throw (IO.userError "inline metadata disappeared")
  for n in inlineNames do
    unless core.findFunction? n |>.isNone do throw (IO.userError s!"inline body retained: {n}")
    unless compiled.circuit.system.findChip? n |>.isNone do throw (IO.userError s!"inline chip retained: {n}")
  for chip in compiled.circuit.system.chips do
    for send in chip.sends do
      if inlineNames.contains send.channel then throw (IO.userError s!"inline send retained: {send.channel}")
  let direct := p.environment.source.checkedHints provider
  let coreHints := HintProvider.checked core.enums provider
  for (name,args,expected) in cases do
    let some entry := p.find? name | throw (IO.userError "missing selected entry")
    let before := p.run name args (hints := direct)
    let after := (Aiur.run core entry.resolved.name args 10000 coreHints).mapError reprStr
    for (mode,actual) in [("source",before),("inlined",after)] do
      unless actual == expected do
        throw (IO.userError s!"{name} ({mode}): expected {repr expected}, got {repr actual}")
  let some entry := p.find? "Main::failed_arg" | throw (IO.userError "missing failure entry")
  unless (p.run "Main::failed_arg" []).toOption.isNone &&
      (Aiur.run core entry.resolved.name []).toOption.isNone do
    throw (IO.userError "inlining discarded an unused argument's failure")
  -- Entry selection must follow aliases to the declaration's modifier.
  for entry in ["Helpers::next","Alias::next","Main::pair"] do
    match Modules.prepare (source.toField Rat) [entry] with
    | .ok _ => throw (IO.userError s!"inline entry accepted: {entry}")
    | .error e => unless (e.splitOn "inline function").length > 1 do
        throw (IO.userError s!"unexpected entry error: {e}")
  -- The source interpreter still calls helpers; it has not expanded their ASTs.
  let some original := p.environment.source.program.findFunction? "Main::shadow" |
    throw (IO.userError "missing original body")
  unless (Generic.sourceCalls [] original.body).any (·.name == "Main::pair") do
    throw (IO.userError "source calls were expanded before semantics")
  IO.println s!"Passed {cases.length} inline execution checks, cycle and entry rejections, and chip checks."

end AiurInlineTests
