import Compilatrix.X86.Types
import Compilatrix.Sem.Result

/-!
# Lir syntax

Lir is the backend's first IR (design note `plans/x86-v2/05-backend.md` §2):
SSA over 64-bit virtual registers, with block parameters instead of φ-nodes,
explicit memory operations over the permissioned byte memory of `X86.State`,
and explicit failure. Runtime procedures are ordinary Lir functions (04 §7),
so calls name a `FunId` and there is no intrinsic.

A function's entry is block 0. Labels are block indices; their order is
semantic, since the clock is charged at every edge whose target label is at
most its source label (`Lir.Semantics`).

Every value is a `Word`. An operation at width `w` reads the low `w` bits of
its operands and produces a zero-extended result. `Base.ctx` names the pinned
context register (`r15`, 04 §6); it is not a virtual register.
-/

namespace Compilatrix.Lir

abbrev VReg := Nat
abbrev Label := Nat
abbrev FunId := Nat
abbrev Word := X86.Word

/-- Operation widths are the machine's (`w8`, `w16`, `w32`, `w64`). -/
abbrev Width := X86.Width

/-- How a narrow load fills the upper bits. -/
inductive Ext where
  | zero
  | sign
  deriving DecidableEq, Repr, Inhabited

/-- An address base: a virtual register or the pinned context register. -/
inductive Base where
  | v (x : VReg)
  | ctx
  deriving DecidableEq, Repr, Inhabited

/-- `base + index·scale + disp`, wrapping modulo 2^64. Well-formed addresses
have a displacement that fits a signed 32-bit field. -/
structure Addr where
  base : Option Base := none
  index : Option (VReg × X86.Scale) := none
  disp : Int := 0
  deriving DecidableEq, Repr, Inhabited

inductive Arg where
  | v (x : VReg)
  | imm (w : Word)
  deriving DecidableEq, Repr, Inhabited

/-- Comparisons on the low `w` bits. `tz`/`tnz`: `a &&& b` is zero / nonzero. -/
inductive Cond where
  | eq | ne
  | ult | ule | ugt | uge
  | slt | sle | sgt | sge
  | tz | tnz
  deriving DecidableEq, Repr, Inhabited

inductive BinOp where
  | add | sub | and | or | xor | mul
  | shl | shr | sar
  | udiv | urem
  deriving DecidableEq, Repr, Inhabited

/-- Unsigned 64-bit overflow tests: carry out of `add`, borrow out of `sub`. -/
inductive Ovf where
  | addC
  | subB
  deriving DecidableEq, Repr, Inhabited

inductive Rhs where
  | arg (a : Arg)
  | bin (o : BinOp) (w : Width) (a b : Arg)
  | load (w : Width) (e : Ext) (m : Addr)
  /-- The effective address (`lea`). -/
  | addr (m : Addr)
  /-- `if c w a b then t else f` (`cmov`); `t` and `f` are whole words. -/
  | select (c : Cond) (w : Width) (a b t f : Arg)
  /-- `1` if `c w a b` holds, else `0` (`setcc`). -/
  | test (c : Cond) (w : Width) (a b : Arg)
  deriving DecidableEq, Repr, Inhabited

inductive Stmt where
  | assign (x : VReg) (r : Rhs)
  /-- Store the low `w` bits of `a`. -/
  | store (w : Width) (m : Addr) (a : Arg)
  /-- Call `f` with `as`, binding its results to `rs`. -/
  | call (rs : List VReg) (f : FunId) (as : List Arg)
  deriving DecidableEq, Repr, Inhabited

/-- A control edge; `args` bind the target block's parameters in parallel. -/
structure Edge where
  target : Label
  args : List Arg := []
  deriving DecidableEq, Repr, Inhabited

inductive Term where
  | jump (e : Edge)
  | br (c : Cond) (w : Width) (a b : Arg) (t f : Edge)
  /-- `x := a ± b` (64-bit), then `ovf` on carry/borrow and `ok` otherwise.
  `x` is defined on both edges, so their arguments may use it. -/
  | brOvf (o : Ovf) (x : VReg) (a b : Arg) (ok ovf : Edge)
  | ret (as : List Arg)
  | tail (f : FunId) (as : List Arg)
  /-- Explicit resource failure (04, roadmap §4.12). -/
  | fail (r : Sem.Resource)
  | trap
  deriving DecidableEq, Repr, Inhabited

structure Block where
  params : List VReg := []
  body : Array Stmt := #[]
  term : Term
  /-- Layout hint: failure and slow paths go last. -/
  cold : Bool := false
  deriving DecidableEq, Repr, Inhabited

/-- Calling convention: internal (05 §6), or a SysV export wrapped at
Stacking. -/
inductive Conv where
  | internal
  | sysvExport (symbol : String)
  deriving DecidableEq, Repr, Inhabited

structure Func where
  /-- Diagnostic and symbol name; not semantic. -/
  name : String := ""
  params : List VReg
  /-- Result arity of every `ret` (and of every function it tail-calls). -/
  results : Nat
  blocks : Array Block
  conv : Conv := .internal
  deriving DecidableEq, Repr, Inhabited

structure Program where
  funcs : Array Func
  main : FunId
  deriving DecidableEq, Repr, Inhabited

/-! ## Reads, writes and edges -/

def Arg.vreg? : Arg → Option VReg
  | .v x => some x
  | .imm _ => none

def Arg.uses (a : Arg) : List VReg := a.vreg?.toList

def argsUses (as : List Arg) : List VReg := as.flatMap Arg.uses

def Base.uses : Base → List VReg
  | .v x => [x]
  | .ctx => []

def Addr.uses (m : Addr) : List VReg :=
  (match m.base with | some b => b.uses | none => []) ++
  (match m.index with | some (x, _) => [x] | none => [])

/-- The virtual registers a right-hand side reads, in operand order. -/
def Rhs.uses : Rhs → List VReg
  | .arg a => a.uses
  | .bin _ _ a b => a.uses ++ b.uses
  | .load _ _ m => m.uses
  | .addr m => m.uses
  | .select _ _ a b t f => a.uses ++ b.uses ++ t.uses ++ f.uses
  | .test _ _ a b => a.uses ++ b.uses

def Stmt.uses : Stmt → List VReg
  | .assign _ r => r.uses
  | .store _ m a => m.uses ++ a.uses
  | .call _ _ as => argsUses as

def Stmt.defs : Stmt → List VReg
  | .assign x _ => [x]
  | .store .. => []
  | .call rs _ _ => rs

def Stmt.addrs : Stmt → List Addr
  | .assign _ (.load _ _ m) | .assign _ (.addr m) | .store _ m _ => [m]
  | _ => []

def Term.edges : Term → List Edge
  | .jump e => [e]
  | .br _ _ _ _ t f => [t, f]
  | .brOvf _ _ _ _ ok ovf => [ok, ovf]
  | .ret _ | .tail .. | .fail _ | .trap => []

def Term.succs (t : Term) : List Label := t.edges.map (·.target)

/-- Replace the edges of a terminator, in `edges` order. A list of the wrong
length leaves the terminator unchanged. -/
def Term.setEdges : Term → List Edge → Term
  | .jump _, [e] => .jump e
  | .br c w a b _ _, [t, f] => .br c w a b t f
  | .brOvf o x a b _ _, [ok, ovf] => .brOvf o x a b ok ovf
  | t, _ => t

theorem Term.setEdges_edges (t : Term) : t.setEdges t.edges = t := by
  cases t <;> rfl

/-- Operand reads of a terminator, before its definition (edge arguments
excluded). -/
def Term.uses : Term → List VReg
  | .jump _ => []
  | .br _ _ a b _ _ => a.uses ++ b.uses
  | .brOvf _ _ a b _ _ => a.uses ++ b.uses
  | .ret as | .tail _ as => argsUses as
  | .fail _ | .trap => []

/-- The terminator's own definition (`brOvf`'s result). -/
def Term.defs : Term → List VReg
  | .brOvf _ x .. => [x]
  | _ => []

/-- Reads of the edge arguments, after the terminator's definition. -/
def Term.edgeUses (t : Term) : List VReg := t.edges.flatMap fun e => argsUses e.args

/-- Every definition in a block, in order: parameters, statements, terminator. -/
def Block.defs (b : Block) : List VReg :=
  b.params ++ b.body.toList.flatMap Stmt.defs ++ b.term.defs

/-- Straight-line size: statements plus the terminator. -/
def Block.size (b : Block) : Nat := b.body.size + 1

def Func.size (f : Func) : Nat := f.blocks.foldl (fun n b => n + b.size) 0

def Program.size (p : Program) : Nat := p.funcs.foldl (fun n f => n + f.size) 0

end Compilatrix.Lir
