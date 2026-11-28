import IxCC.Fir.Syntax

/-! # Dead-arm constructor allocation sinking (`Own.Plain.Sink`)

A pure, deterministic `Fir.Program → Fir.Program` pass run at the RC front-end
boundary before ownership placement (`Own.Plain.Live` / `Own.Plain.checkOwned`):

When a constructor allocation `x := C [args]` directly precedes a multi-arm
`case s alts dflt` (`s ≠ x`) and `x` is free in **exactly one** arm of the
`case`, `sinkBind` sinks `x := C [args]` into that single arm (recursing into
nested `case`s inside that arm). Bottom-up traversal (`sinkCode`) sinks chains
of constructor bindings in order without duplicating code size.

Because constructor allocation is pure in `Fir.Semantics` and `case` binds no
variables, sinking eliminates dead-arm allocations and their corresponding RC
`inc`/`dec` pairs (for example, `reverse`'s specialized `append v0 [v1]`) while
preserving exact `Fir.eval` semantics (`Own.Plain.Proof.Sink`). -/

set_option autoImplicit false

namespace IxCC.Own.Plain.Sink

open IxCC.Fir (Var Arg Rhs Code Alt Fun Program CtorInfo)

def argHas (x : Var) : Arg → Bool
  | .var y => y == x
  | _ => false

def argsHas (x : Var) : List Arg → Bool
  | [] => false
  | a :: as => argHas x a || argsHas x as

def rhsHas (x : Var) : Rhs → Bool
  | .arg a => argHas x a
  | .ctor _ as | .prim _ as | .call _ as => argsHas x as
  | .proj y _ _ => y == x

mutual
/-- Whether variable `x` occurs free in `c`. -/
def freeInCode (x : Var) : Code → Bool
  | .bind y r k => rhsHas x r || (y != x && freeInCode x k)
  | .jp _ ps _ body k => (!ps.contains x && freeInCode x body) || freeInCode x k
  | .jmp _ as => argsHas x as
  | .case s alts d => (s == x) || freeInAlts x alts || freeInOpt x d
  | .ret a => argHas x a
  | .tcall _ as => argsHas x as
  | .trap => false

def freeInAlts (x : Var) : List Alt → Bool
  | [] => false
  | .mk _ body :: rest => freeInCode x body || freeInAlts x rest

def freeInOpt (x : Var) : Option Code → Bool
  | none => false
  | some c => freeInCode x c
end

def countAltsUses (x : Var) : List Alt → Nat
  | [] => 0
  | .mk _ b :: rest => (if freeInCode x b then 1 else 0) + countAltsUses x rest

def countArmUses (x : Var) (alts : List Alt) (dflt : Option Code) : Nat :=
  countAltsUses x alts + match dflt with
    | some d => if freeInCode x d then 1 else 0
    | none => 0

def numArms (alts : List Alt) (dflt : Option Code) : Nat :=
  alts.length + if dflt.isSome then 1 else 0

mutual
/-- Sink `.bind x (.ctor c args)` into the unique arm of a multi-arm `case`
where `x` occurs free, recursing into nested `case`s inside that arm. -/
def sinkBind (x : Var) (c : CtorInfo) (args : List Arg) : Code → Code
  | .case s alts dflt =>
    if s != x && numArms alts dflt ≥ 2 && countArmUses x alts dflt == 1 then
      .case s (sinkBindAlts x c args alts) (sinkBindOpt x c args dflt)
    else
      .bind x (.ctor c args) (.case s alts dflt)
  | k => .bind x (.ctor c args) k

def sinkBindAlts (x : Var) (c : CtorInfo) (args : List Arg) : List Alt → List Alt
  | [] => []
  | .mk k b :: rest =>
    .mk k (if freeInCode x b then sinkBind x c args b else b) :: sinkBindAlts x c args rest

def sinkBindOpt (x : Var) (c : CtorInfo) (args : List Arg) : Option Code → Option Code
  | none => none
  | some d => some (if freeInCode x d then sinkBind x c args d else d)
end

mutual
/-- Bottom-up dead-arm constructor allocation sinking over `Fir.Code`. -/
def sinkCode : Code → Code
  | .bind x (.ctor c args) k => sinkBind x c args (sinkCode k)
  | .bind x r k => .bind x r (sinkCode k)
  | .jp j ps rec body k => .jp j ps rec (sinkCode body) (sinkCode k)
  | .case s alts dflt => .case s (sinkAlts alts) (sinkOpt dflt)
  | .jmp j args => .jmp j args
  | .ret a => .ret a
  | .tcall f args => .tcall f args
  | .trap => .trap

def sinkAlts : List Alt → List Alt
  | [] => []
  | .mk k b :: rest => .mk k (sinkCode b) :: sinkAlts rest

def sinkOpt : Option Code → Option Code
  | none => none
  | some c => some (sinkCode c)
end

def sinkFun (fd : Fun) : Fun :=
  { fd with body := sinkCode fd.body }

/-- Sink dead-arm constructor allocations across every function of `F`. -/
def run (F : Program) : Program :=
  { F with funs := F.funs.map sinkFun }

end IxCC.Own.Plain.Sink
