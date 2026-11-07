import IxCC.Cfg.Rc.Lower

set_option autoImplicit false
namespace IxCC.Cfg.Rc


def argBound (first : Nat) : Fir.Arg → Bool
  | .var x => decide (x < first)
  | .lit _ | .erased => true

def actionBound (first : Nat) : Action → Bool
  | .inc x _ | .dec x => decide (x < first)

def rhsBound (limit first : Nat) : Own.Rhs → Bool
  | .fir (.arg a) => argBound first a
  | .fir (.prim _ args) => args.all (argBound first)
  | .fir (.call f args) => decide (f < limit) && args.all (argBound first)
  | .fir _ => false
  | .alloc _ args _ => args.all (argBound first)
  | .proj x _ _ => decide (x < first)

def instrBound (limit first : Nat) (i : Instr) : Bool :=
  if reserved limit i then
    match decode limit i with
    | some (slot, a) => decide (first ≤ slot) && actionBound first a
    | none => false
  else match i with
    | .bind x rhs => decide (x < first) && rhsBound limit first rhs

def edgeBound (first blocks : Nat) (e : Edge) : Bool :=
  decide (e.target < blocks) && e.args.all (argBound first)

def termBound (limit first blocks : Nat) : Term → Bool
  | .jump e => edgeBound first blocks e
  | .switch x alts d => decide (x < first) &&
      alts.all (fun a => edgeBound first blocks a.2) && d.toList.all (edgeBound first blocks)
  | .ret a => argBound first a
  | .tcall f args => decide (f < limit) && args.all (argBound first)
  | .trap => true

def functionBounds (limit first : Nat) (fd : Cfg.Fun) : Bool :=
  fd.blocks.all fun b => b.params.all (fun p => decide (p.1 < first)) &&
    b.body.all (instrBound limit first) && termBound limit first fd.blocks.length b.term

end IxCC.Cfg.Rc
