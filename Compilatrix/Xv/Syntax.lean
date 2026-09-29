import Compilatrix.Lir.Syntax
import Compilatrix.X86.Table.Rows

/-!
# Xv and Xl syntax

The machine-instruction IRs between Lir and typed x86 (design note
`plans/x86-v2/05-backend.md` §3). One syntax, parameterised by the operand
type `ρ`, serves both levels:

- **Xv** (`Program VReg`): x86 instructions over Lir's virtual registers, as
  selection emits them. It is three-address: a tie between a row's
  read-write slot and its definition is operand metadata (`Con.reuse`), not
  syntax, so `x := a + 8` is `op addMI8 [x] [r a, i 8]` with `x` reusing `a`.
- **Xl** (`Program Loc`): the same instructions over locations (registers,
  frame slots and argument cells), as allocation produces them.

Xv and Xl keep Lir's labels, calls and clock charges, so the three levels
run in lock-step (05 §2, §5).

**Instructions.** `op o defs args` is one table row `o`; `fused p pargs c
defs cargs` a flag producer and consumer that no edit may separate;
`move` a copy; `zero x` the `xor x32, x32` idiom, which has no uses (a
divergence from 05 §3, which leaves the idiom's form open); `call f args
rets` a call whose operands the convention fixes. Terminators are `jmp`,
`jcc p pargs defs c t f` (the flag producer `p` and the condition `c`; its
definitions reach both edges, for `brOvf`), `ret`, `tail`, `fail` and
`trap`.

**Operand layout of a row** (`Xv.bindSlots`). `args` holds one
entry per slot that the row reads or addresses, and one per written slot
whose operand is memory; `defs` holds one register per written slot whose
operand is a register. A read-write slot with a register argument is a tie:
its argument is a use and its definition the next entry of `defs`. The
table's implicit register operands (from M1.B1: `div`'s `rax`/`rdx`, a
shift's `cl`) follow the slots in the same way, fixed to their registers.
-/

namespace Compilatrix.Xv

open Compilatrix.Lir (VReg Label FunId Word)

/-- An Xl location. `slot i` is the `i`-th cell of the frame; `inArg i` and
`outArg i` are the incoming and outgoing stack-argument cells (8 bytes
each) past the convention's seven argument registers. -/
inductive Loc where
  | reg (r : X86.GPR)
  | slot (i : Nat)
  | inArg (i : Nat)
  | outArg (i : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- A stack cell: a slot or an argument cell. -/
def Loc.isCell : Loc → Bool
  | .reg _ => false
  | _ => true

/-- An address base: an operand or the pinned context register (`r15`). -/
inductive Base (ρ : Type) where
  | r (x : ρ)
  | ctx
  deriving DecidableEq, Repr, Inhabited

/-- `base + index·scale + disp`, wrapping modulo 2^64. -/
structure Amode (ρ : Type) where
  base : Option (Base ρ) := none
  index : Option (ρ × X86.Scale) := none
  disp : Int32 := 0
  deriving DecidableEq, Repr, Inhabited

/-- A context access of `bytes` bytes that may reach the `entrySp` or
`stackLimit` cell (`ctx − 64`, `ctx − 56`), which the failure exit and the
prologue read (05 §6.1); no store may (`Lir.WellFormed` condition 7). -/
def Amode.hitsProtectedCtx {ρ : Type} (m : Amode ρ) (bytes : Nat) : Bool :=
  (match m.base with | some .ctx => true | _ => false) && decide (m.disp.toInt < -48) &&
    (m.index.isSome || decide (-64 < m.disp.toInt + bytes))

/-- A row argument. Immediates are 64-bit words in the row's canonical form
(`X86.ArgKind.accepts`). -/
inductive XArg (ρ : Type) where
  | r (x : ρ)
  | m (a : Amode ρ)
  | i (w : Word)
  deriving DecidableEq, Repr, Inhabited

inductive Inst (ρ : Type) where
  /-- One table row, three-address. -/
  | op (o : X86.Op) (defs : List ρ) (args : List (XArg ρ))
  /-- A flag producer `p` (no definitions) and a flag consumer `c`, executed
  as one instruction. -/
  | fused (p : X86.Op) (pargs : List (XArg ρ)) (c : X86.Op) (defs : List ρ) (cargs : List (XArg ρ))
  /-- A copy. At Xl, allocation edits are moves too. -/
  | move (dst src : ρ)
  /-- `xor x32, x32`: `x := 0`, with no uses. -/
  | zero (x : ρ)
  /-- A call; arguments and results sit where the convention puts them. -/
  | call (f : FunId) (args rets : List ρ)
  deriving DecidableEq, Repr, Inhabited

/-- A control edge; `args` bind the target's parameters in parallel. At Xl
the allocator's edits replace them, and both lists are usually empty. -/
structure Edge (ρ : Type) where
  target : Label
  args : List ρ := []
  deriving DecidableEq, Repr, Inhabited

inductive Term (ρ : Type) where
  | jmp (e : Edge ρ)
  /-- Run the producer row `p` (defining `defs`), then branch on `c`. -/
  | jcc (p : X86.Op) (pargs : List (XArg ρ)) (defs : List ρ) (c : X86.Condition) (t f : Edge ρ)
  | ret (vs : List ρ)
  | tail (f : FunId) (args : List ρ)
  | fail (r : Sem.Resource)
  | trap
  deriving DecidableEq, Repr, Inhabited

structure Block (ρ : Type) where
  params : List ρ := []
  body : Array (Inst ρ) := #[]
  term : Term ρ
  cold : Bool := false
  deriving DecidableEq, Repr, Inhabited

structure Func (ρ : Type) where
  name : String := ""
  params : List ρ
  results : Nat
  blocks : Array (Block ρ)
  conv : Lir.Conv := .internal
  deriving DecidableEq, Repr, Inhabited

structure Program (ρ : Type) where
  funcs : Array (Func ρ)
  main : FunId
  deriving DecidableEq, Repr, Inhabited

/-- Xv: instructions over virtual registers. -/
abbrev VProgram := Program VReg

/-- Xl: instructions over locations. -/
abbrev LProgram := Program Loc

/-! ## Reads, writes and edges -/

variable {ρ : Type}

def Amode.regs (a : Amode ρ) : List ρ :=
  (match a.base with | some (.r x) => [x] | _ => []) ++
  (match a.index with | some (x, _) => [x] | none => [])

def XArg.regs : XArg ρ → List ρ
  | .r x => [x]
  | .m a => a.regs
  | .i _ => []

def xargsRegs (as : List (XArg ρ)) : List ρ := as.flatMap XArg.regs

/-- The operands an instruction reads, in argument order. -/
def Inst.uses : Inst ρ → List ρ
  | .op _ _ args => xargsRegs args
  | .fused _ pargs _ _ cargs => xargsRegs pargs ++ xargsRegs cargs
  | .move _ src => [src]
  | .zero _ => []
  | .call _ args _ => args

def Inst.defs : Inst ρ → List ρ
  | .op _ defs _ => defs
  | .fused _ _ _ defs _ => defs
  | .move dst _ => [dst]
  | .zero x => [x]
  | .call _ _ rets => rets

def Term.edges : Term ρ → List (Edge ρ)
  | .jmp e => [e]
  | .jcc _ _ _ _ t f => [t, f]
  | .ret _ | .tail .. | .fail _ | .trap => []

def Term.succs (t : Term ρ) : List Label := t.edges.map (·.target)

/-- Reads of a terminator before its definitions (edge arguments excluded). -/
def Term.uses : Term ρ → List ρ
  | .jcc _ pargs _ _ _ _ => xargsRegs pargs
  | .ret vs => vs
  | .tail _ args => args
  | .jmp _ | .fail _ | .trap => []

def Term.defs : Term ρ → List ρ
  | .jcc _ _ defs _ _ _ => defs
  | _ => []

/-- Reads of the edge arguments, after the terminator's definitions. -/
def Term.edgeUses (t : Term ρ) : List ρ := t.edges.flatMap (·.args)

def Block.size (b : Block ρ) : Nat := b.body.size + 1

def Func.size (f : Func ρ) : Nat := f.blocks.foldl (fun n b => n + b.size) 0

def Program.size (p : Program ρ) : Nat := p.funcs.foldl (fun n f => n + f.size) 0

end Compilatrix.Xv
