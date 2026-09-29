import Compilatrix.Xv.Syntax
import Compilatrix.X86.Table.Exec

/-!
# Row operands and row execution

How an Xv/Xl instruction's `defs` and `args` fill a table row's slots
(`bindSlots`), and how the row then runs: every row executes through the
table's `Op.exec`, the one x86 semantics that the typed and byte machines
also use (05 §3, §8.1).

**Binding.** Slots are filled in order. A read or address slot takes the
next argument. A read-write slot takes the next argument: a register is a
tie (a use, and the next definition, which shares its location), a memory
operand is read and written in place. A write slot takes the next argument
if it is a memory operand the slot accepts, and otherwise the next
definition. Both lists must be used up. No row has two memory-capable slots,
so the layout is unambiguous. (M1.B1's implicit register operands will bind
after the slots, fixed to their registers.)

**Execution.** A row runs on a machine core in which each operand occupies
a register (`place`): the instruction reads all its uses, runs the row, and
reads its definitions back from their registers; the tied definition from
its use's register. Xv chooses the registers (`Xv.assignRegs`); Xl's
locations are registers already, and stack cells borrow scratch registers
(`Xv.Xl.execBound`).
-/

namespace Compilatrix.Xv

open Compilatrix.Lir (VReg Word)

variable {ρ : Type}

/-- One slot of a row, filled. -/
inductive Bound (ρ : Type) where
  /-- A read or address slot and its argument. -/
  | input (s : X86.Slot) (a : XArg ρ)
  /-- A written slot with a register destination: the definition. -/
  | output (s : X86.Slot) (x : ρ)
  /-- A read-write slot with a register argument: the use `a` and the
  definition `x`, which share a location (`Con.reuse`). -/
  | tied (s : X86.Slot) (a x : ρ)
  /-- A written or read-write slot with a memory operand. -/
  | memory (s : X86.Slot) (m : Amode ρ)
  deriving DecidableEq, Repr, Inhabited

def bindSlots : List X86.Slot → List ρ → List (XArg ρ) → Option (List (Bound ρ))
  | [], [], [] => some []
  | [], _, _ => none
  | s :: ss, defs, args =>
      match s.role, args, defs with
      | .read, a :: args, defs | .address, a :: args, defs =>
          (Bound.input s a :: ·) <$> bindSlots ss defs args
      | .readWrite, .r a :: args, x :: defs => (Bound.tied s a x :: ·) <$> bindSlots ss defs args
      | .readWrite, .m m :: args, defs => (Bound.memory s m :: ·) <$> bindSlots ss defs args
      | .write, .m m :: args, defs =>
          if s.kinds.contains .mem then (Bound.memory s m :: ·) <$> bindSlots ss defs args
          else match defs with
            | x :: defs => (Bound.output s x :: ·) <$> bindSlots ss defs (.m m :: args)
            | [] => none
      | .write, args, x :: defs => (Bound.output s x :: ·) <$> bindSlots ss defs args
      | _, _, _ => none

/-- The slots of row `o` filled with `defs` and `args`. -/
def bindRow (o : X86.Op) (defs : List ρ) (args : List (XArg ρ)) : Option (List (Bound ρ)) :=
  bindSlots (X86.desc o).slots defs args

/-- Operands the bound slots read, in slot order (addresses included). -/
def Bound.uses : Bound ρ → List ρ
  | .input _ a => a.regs
  | .output _ _ => []
  | .tied _ a _ => [a]
  | .memory _ m => m.regs

def Bound.defs : Bound ρ → List ρ
  | .output _ x | .tied _ _ x => [x]
  | _ => []

/-! ## The machine view -/

/-- `rsp` has no index encoding. -/
def indexReg : X86.GPR → Option X86.IndexReg
  | .rax => some .rax | .rcx => some .rcx | .rdx => some .rdx | .rbx => some .rbx
  | .rsp => none | .rbp => some .rbp | .rsi => some .rsi | .rdi => some .rdi
  | .r8 => some .r8 | .r9 => some .r9 | .r10 => some .r10 | .r11 => some .r11
  | .r12 => some .r12 | .r13 => some .r13 | .r14 => some .r14 | .r15 => some .r15

/-- The machine address of an addressing mode whose registers sit at
`place`; the context base is `r15`. Scale is normalised without an index. -/
def Amode.toMem (place : ρ → Option X86.GPR) (a : Amode ρ) : Option X86.MemAddr := do
  let base ← match a.base with
    | none => pure none
    | some .ctx => pure (some X86.GPR.r15)
    | some (.r x) => some <$> place x
  let (index, scale) ← match a.index with
    | none => pure (none, X86.Scale.one)
    | some (x, s) => do
        let r ← place x
        let i ← indexReg r
        pure (some i, s)
  pure { base, index, scale, displacement := a.disp.toUInt32 }

/-- A bound slot's machine operand. `addr` places address registers, which
must be registers even at Xl. -/
def Bound.machine (place addr : ρ → Option X86.GPR) : Bound ρ → Option X86.Arg
  | .input _ (.r x) => .reg <$> place x
  | .input _ (.m a) => .mem <$> a.toMem addr
  | .input _ (.i w) => some (.imm w)
  | .output _ x => .reg <$> place x
  | .tied _ a _ => .reg <$> place a
  | .memory _ m => .mem <$> m.toMem addr

/-- Where each definition is read back after the row. -/
def Bound.readback (place : ρ → Option X86.GPR) : Bound ρ → List (ρ × Option X86.GPR)
  | .output _ x => [(x, place x)]
  | .tied _ a x => [(x, place a)]
  | _ => []

/-- The distinct elements of a list, in order of first appearance. -/
def dedup {α : Type} [BEq α] : List α → List α
  | [] => []
  | x :: xs => x :: (dedup xs).filter (· != x)

/-- A row's outcome, with the fault turned into `none` (a stuck step:
Lir's success implies each row's precondition, 05 §2). -/
def execRow (o : X86.Op) (args : List X86.Arg) (core : X86.Core) (flags : X86.ByteEval.Flags) :
    Option (X86.Core × X86.ByteEval.Flags) :=
  match o.exec args core flags with
  | .ok r => some r
  | .error _ => none

/-- Run rows in sequence on one core, threading the flags from `{}` (the
typed machine's undefined flags). -/
def execRows (parts : List (X86.Op × List X86.Arg)) (core : X86.Core) :
    Option (X86.Core × X86.ByteEval.Flags) :=
  parts.foldlM (init := (core, {})) fun (core, flags) (o, args) => execRow o args core flags

/-- Whether the `jcc` row with condition `c` is taken under `flags`: that
row's own semantics, on the flags it declares. `none` if a flag it reads is
undefined. -/
def jccTaken (c : X86.Condition) (flags : X86.ByteEval.Flags) : Option Bool :=
  let row := X86.desc (X86.Op.jccRel32 c)
  match row.sem ⟨[], flags.restrict row.flagsIn⟩ with
  | .ok out => out.taken
  | .error _ => none

/-- The registers an Xv instruction's operands may occupy: every
general-purpose register except `rsp`, `rbp` and the context register
`r15`. -/
def scratch : List X86.GPR :=
  [.rax, .rcx, .rdx, .rbx, .rsi, .rdi, .r8, .r9, .r10, .r11, .r12, .r13, .r14]

/-- A register's position in `allGPRs` (its encoding number). -/
def gprIndex : X86.GPR → Nat
  | .rax => 0 | .rcx => 1 | .rdx => 2 | .rbx => 3 | .rsp => 4 | .rbp => 5 | .rsi => 6 | .rdi => 7
  | .r8 => 8 | .r9 => 9 | .r10 => 10 | .r11 => 11 | .r12 => 12 | .r13 => 13 | .r14 => 14 | .r15 => 15

def allGPRs : List X86.GPR :=
  [.rax, .rcx, .rdx, .rbx, .rsp, .rbp, .rsi, .rdi, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15]

end Compilatrix.Xv
