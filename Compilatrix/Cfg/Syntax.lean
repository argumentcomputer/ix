import Compilatrix.Own.Syntax

/-! # Cfg syntax

The control-flow IR between Own and Lir (design note 03 §7, OWN-4), in the
Phase 1 fragment: blocks with parameters, a straight-line body and a
terminator.

* A function's **entry is block 0**; its parameters are the function's.
* `Instr.bind x rhs` runs an Own right-hand side; a call (`fir (call f
  as)`) is a non-tail call that returns to the next instruction.
* An `Edge` binds its target's parameters; `back` marks a **back edge**,
  which charges the clock: exactly Own's self tail calls (a jump to block
  0) and recursive jumps (03 C6, 06 S30).
* `switch x alts dflt` selects an edge by constructor key (a `Nat` peels);
  `ret`, `tcall` (to another function) and `trap` end a block.

`Cfg.lower` numbers blocks so that every forward edge goes to a higher
label and every back edge to a lower or equal one, which is the order
04's `Rt.lower` needs (a back edge becomes a backward Lir edge, 06 S32).
Critical edges are allowed (`Rt.lower` splits them, 06 S14). The RC
instructions (`inc`, `dec`, `takeUnique`, `dropCredit`, `freeze`), credits
and `branchShared` of 03 §7 are Phase 2. -/

namespace Compilatrix.Cfg

open Compilatrix.Fir (Var FunId Arg)

abbrev BlockId := Nat

inductive Instr where
  | bind (x : Var) (rhs : Own.Rhs)
  deriving DecidableEq, Repr, Inhabited

structure Edge where
  target : BlockId
  args : List Arg := []
  back : Bool := false
  deriving DecidableEq, Repr, Inhabited

inductive Term where
  | jump (e : Edge)
  | switch (x : Var) (alts : List (Key.CtorKey × Edge)) (dflt : Option Edge)
  | ret (a : Arg)
  | tcall (f : FunId) (args : List Arg)
  | trap
  deriving DecidableEq, Repr, Inhabited

structure Block where
  params : List (Var × Own.PSig) := []
  body : List Instr := []
  term : Term
  deriving DecidableEq, Repr, Inhabited

structure Fun where
  key : Key.GKey
  sig : Own.Sig
  /-- Block 0 is the entry; its parameters are the function's. -/
  blocks : List Block
  regionFrame : Bool := false
  /-- Variables are below `vars` (Own's supply). -/
  vars : Nat := 0
  deriving Inhabited

structure Program where
  funs : Src.NatMap Fun
  size : Nat
  exports : List FunId
  ctors : List Lam.CtorInfo
  known : Lam.Known
  deriving Inhabited

namespace Fun

def block? (fd : Fun) (b : BlockId) : Option Block := fd.blocks[b]?

def params (fd : Fun) : List Var := ((fd.blocks.head?.map (·.params)).getD []).map (·.1)

/-- Instructions plus one per terminator. -/
def size (fd : Fun) : Nat := fd.blocks.foldl (fun n b => n + b.body.length + 1) 0

end Fun

namespace Term

def edges : Term → List Edge
  | .jump e => [e]
  | .switch _ alts d => alts.map (·.2) ++ d.toList
  | .ret _ | .tcall .. | .trap => []

end Term

namespace Program

def fun? (P : Program) (f : FunId) : Option Fun := P.funs.get? f

def funList (P : Program) : List (FunId × Fun) :=
  (List.range P.size).filterMap fun f => (P.fun? f).map (f, ·)

def blocks (P : Program) : Nat := P.funList.foldl (fun n (_, fd) => n + fd.blocks.length) 0

/-- Instructions plus terminators, over all functions. -/
def instrs (P : Program) : Nat := P.funList.foldl (fun n (_, fd) => n + fd.size) 0

end Program

end Compilatrix.Cfg
