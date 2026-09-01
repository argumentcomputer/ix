module

public import LSpec
public import Ix.Aiur

/-!
`const NAME: T = body` declarations: direct substitution in terms (`.NAME`
is the body) and in patterns (`.NAME` is the pattern read off the body,
`store(v)` becoming the pointer pattern `&v`), so an interface consumer can
match on a constant without knowing its representation. Negative cases: a
computed const used as a pattern, and a const cycle, are compile errors.
-/

public section

open LSpec Aiur

namespace AiurTests.Const

def program : Source.Toplevel := ⟦
  enum Opt {
    Some(G),
    None
  }

  fn id(x: G) -> G { x }

  const ZERO: G = 0
  const ONE: G = 1
  const PAIR: (G, G) = (.ZERO, .ONE)
  const BYTES: &[U8; 2] = store([1u8, 2u8])
  const NONE: Opt = Opt.None
  const SOME_ONE: Opt = Opt.Some(.ONE)
  const NESTED: [&[U8; 2]; 2] = [.BYTES, .BYTES]
  -- Computed: usable in terms only.
  const COMPUTED: G = id(41)

  pub fn match_field(x: G) -> G {
    match x {
      .ZERO => 10,
      .ONE => 11,
      _ => 12,
    }
  }

  pub fn match_pair(a: G, b: G) -> G {
    match (a, b) {
      .PAIR => 1,
      _ => 0,
    }
  }

  fn is_bytes(p: &[U8; 2]) -> G {
    match p {
      .BYTES => 1,
      _ => 0,
    }
  }

  pub fn match_ptr() -> G {
    is_bytes(store([1u8, 2u8])) + 2 * is_bytes(store([2u8, 2u8]))
  }

  fn opt_code(o: Opt) -> G {
    match o {
      .SOME_ONE => 1,
      .NONE => 2,
      _ => 3,
    }
  }

  pub fn match_ctor() -> G {
    opt_code(Opt.Some(1)) + 10 * opt_code(Opt.None) + 100 * opt_code(Opt.Some(7))
  }

  fn nested(x: [&[U8; 2]; 2]) -> G {
    match x {
      .NESTED => 1,
      _ => 0,
    }
  }

  pub fn match_nested() -> G {
    nested([store([1u8, 2u8]), store([1u8, 2u8])])
      + 2 * nested([store([1u8, 2u8]), store([0u8, 2u8])])
  }

  pub fn const_term() -> G { .ONE + .ONE + .ZERO }

  pub fn const_let() -> G {
    let (a, b) = .PAIR;
    a + 2 * b
  }

  pub fn computed_term() -> G { .COMPUTED + 1 }
⟧

def computedPattern : Source.Toplevel := ⟦
  fn id(x: G) -> G { x }
  const BAD: G = id(1)
  pub fn f(x: G) -> G {
    match x {
      .BAD => 1,
      _ => 0,
    }
  }
⟧

def cyclic : Source.Toplevel := ⟦
  const A: G = .B
  const B: G = .A
  pub fn f(x: G) -> G {
    match x {
      .A => 1,
      _ => 0,
    }
  }
⟧

def run (compiled : CompiledToplevel) (name : Lean.Name) (input : Array Aiur.G) : Option Aiur.G := do
  let idx ← compiled.getFuncIdx name
  match compiled.bytecode.execute idx input default with
  | .error _ => none
  | .ok (output, _, _) => output[0]?

def compileError (t : Source.Toplevel) (needle : String) : Bool :=
  match t.compile with
  | .error e => (e.splitOn needle).length > 1
  | .ok _ => false

def tests : TestSeq :=
  match program.compile with
  | .error e => test s!"const program compiles: {e}" false
  | .ok c =>
    let g := Aiur.G.ofNat
    test "field const patterns" (run c `match_field #[g 0] == some (g 10)
      && run c `match_field #[g 1] == some (g 11)
      && run c `match_field #[g 5] == some (g 12)) ++
    test "tuple const pattern (of consts)" (run c `match_pair #[g 0, g 1] == some (g 1)
      && run c `match_pair #[g 1, g 1] == some (g 0)) ++
    test "stored const matches by contents (`store` ↦ `&` pattern)" (run c `match_ptr #[] == some (g 1)) ++
    test "constructor const patterns" (run c `match_ctor #[] == some (g 321)) ++
    test "nested stored consts" (run c `match_nested #[] == some (g 1)) ++
    test "consts in terms" (run c `const_term #[] == some (g 2)) ++
    test "const in a let pattern" (run c `const_let #[] == some (g 2)) ++
    test "computed const in a term" (run c `computed_term #[] == some (g 42)) ++
    test "computed const in a pattern is rejected"
      (compileError computedPattern "not usable as a pattern") ++
    test "cyclic consts are rejected" (compileError cyclic "cyclic")

end AiurTests.Const
