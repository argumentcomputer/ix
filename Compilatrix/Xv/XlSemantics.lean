import Compilatrix.Xv.Semantics
import Compilatrix.Lir.Operands

/-!
# Xl semantics

Xl is Xv over locations (05 §3): registers, a frame's slots, and its
incoming and outgoing stack-argument cells. Registers are global
(`GPR → Option Word`); each frame owns its cells. Labels, calls and the
clock are Xv's, so allocation's edits (moves) are ordinary steps that the
clock ignores, and Xv and Xl time out at the same clock.

**Calls** re-derive CompCert's `return_regs` (05 §3): a call's arguments
must sit in the convention's locations (`rdi rsi rdx rcx r8 r9 r10`, then
outgoing cells, which become the callee's incoming cells), and its results
in `rax rdx`. The callee starts with only its arguments defined. On return
the caller sees the results, `none` in the callee's clobber set
(`Env.clobbers`, every caller-saved register unless a runtime procedure
declares fewer, 04 §7), and its own values elsewhere, which covers the
callee-saved registers; its outgoing cells are gone. So the allocator never
reasons about saving registers, and Stacking proves the callee-saved
registers are restored. A tail call passes register arguments only (stack
arguments force a call and a return, 05 §6).

**Rows** run through the same executor as Xv, with each register location
as itself. A stack cell in an r/m slot borrows a scratch register the
instruction does not name; it may be read at any width, since a row's
results depend only on the low `width` bits of its inputs, but written only
at width 64, where a register write and an 8-byte memory write agree (a
narrower definition must be `reg`, `Xv.Operands`). A tied definition must
sit at its use's location, an implicit operand at its fixed register,
address registers must be registers, and no operand may be `rsp`, `rbp` or
the context register `r15` (05 §5). A fused `setcc` zeroes its destination
register first, as its expansion's `xor` does, so that register must not
hold any of the pair's uses (an early definition). Any other case is
`stuck`, which the validator's constraint checks exclude.
-/

namespace Compilatrix.Xv.Xl

open Compilatrix.Lir (VReg Label FunId Word)
open Compilatrix.Xv

/-- Registers, indexed by `gprIndex`; `none` is unknown. -/
abbrev Regs := Array (Option Word)

def Regs.empty : Regs := Array.replicate 16 none

def Regs.get (rs : Regs) (r : X86.GPR) : Option Word := (rs[gprIndex r]?).join

def Regs.set (rs : Regs) (r : X86.GPR) (v : Option Word) : Regs := rs.set! (gprIndex r) v

/-- The calling-convention parameters of an Xl run. -/
structure Env where
  /-- Registers a call to each function may change (besides its results). -/
  clobbers : FunId → List X86.GPR := fun _ => X86.SysV.callerSaved.toList

/-- Registers no Xl operand may name: the stack pointer, the frame pointer
(never written, 05 §6) and the context register. -/
def reserved (r : X86.GPR) : Bool := r == .rsp || r == .rbp || r == .r15

/-- The internal convention.s argument registers (seven) and result registers (two). -/
def nArgRegs : Nat := List.length Lir.Conv.argRegs
def nResultRegs : Nat := List.length Lir.Conv.resultRegs

/-- The caller's location of the `i`-th call argument. -/
def argLoc (i : Nat) : Loc :=
  match Lir.Conv.argRegs[i]? with
  | some r => .reg r
  | none => .outArg (i - nArgRegs)

/-- The callee's location of its `i`-th parameter. -/
def paramLoc (i : Nat) : Loc :=
  match Lir.Conv.argRegs[i]? with
  | some r => .reg r
  | none => .inArg (i - nArgRegs)

/-- The location of the `i`-th result: `rax`, then `rdx`. -/
def resultLoc (i : Nat) : Option Loc := (Lir.Conv.resultRegs[i]?).map .reg

structure Frame where
  fn : FunId
  label : Label
  /-- The next instruction; `body.size` is the terminator. -/
  pos : Nat
  slots : Std.HashMap Nat Word := {}
  inArgs : Array Word := #[]
  outArgs : Std.HashMap Nat Word := {}
  /-- For a suspended caller: its registers at the call. -/
  saved : Regs := Regs.empty
  /-- For a suspended caller: the callee's clobber set. -/
  clobber : List X86.GPR := []
  /-- For a suspended caller: how many results the call binds. -/
  results : Nat := 0

structure State where
  mem : X86.Memory
  ctx : Word
  regs : Regs
  /-- The running frame first. -/
  stack : List Frame

def read (regs : Regs) (fr : Frame) : Loc → Option Word
  | .reg r => if reserved r then none else regs.get r
  | .slot i => fr.slots[i]?
  | .inArg i => fr.inArgs[i]?
  | .outArg i => fr.outArgs[i]?

def write (regs : Regs) (fr : Frame) (l : Loc) (v : Word) : Option (Regs × Frame) :=
  match l with
  | .reg r => if reserved r then none else some (regs.set r (some v), fr)
  | .slot i => some (regs, { fr with slots := fr.slots.insert i v })
  | .inArg i => if i < fr.inArgs.size then some (regs, { fr with inArgs := fr.inArgs.set! i v }) else none
  | .outArg i => some (regs, { fr with outArgs := fr.outArgs.insert i v })

def readAll (regs : Regs) (fr : Frame) (ls : List Loc) : Option (List Word) := ls.mapM (read regs fr)

/-- Write values to locations in order (a parallel move once the values are
read). -/
def writeAll (regs : Regs) (fr : Frame) : List Loc → List Word → Option (Regs × Frame)
  | [], [] => some (regs, fr)
  | l :: ls, v :: vs => do
      let (regs, fr) ← write regs fr l v
      writeAll regs fr ls vs
  | _, _ => none

/-- Whether a bound operand's locations are encodable (see the module note):
stack cells only in r/m slots (written only at width 64), ties at their
use's location, implicit operands at their fixed register. -/
def Bound.placeable : Bound Loc → Bool
  | .input s (.r l) => !l.isCell || s.kinds.contains .mem
  | .output s l => !l.isCell || (s.kinds.contains .mem && s.width == .w64)
  | .tied s a x => a == x && (!a.isCell || (s.kinds.contains .mem && s.width == .w64))
  | .fixedUse i a => a == .reg i.reg
  | .fixedDef i x => x == .reg i.reg
  | .fixedTied i a x => a == .reg i.reg && x == .reg i.reg
  | _ => true

def Bound.locs : Bound Loc → List Loc
  | .input _ a => a.regs
  | .output _ x | .fixedDef _ x => [x]
  | .tied _ a x | .fixedTied _ a x => [a, x]
  | .fixedUse _ a => [a]
  | .memory _ m => m.regs

/-- Run rows whose slots are bound over locations, on one core: new
registers, frame, memory and flags. With `zeroFirst`, the last row's narrow
register outputs (a fused `setcc`) are zeroed before the rows run, as the
expansion's `xor` does; each is an early definition, so it must not share a
location with any use. -/
def execBound (parts : List (X86.Op × List (Bound Loc))) (regs : Regs) (fr : Frame)
    (mem : X86.Memory) (ctx : Word) (zeroFirst : Bool := false) :
    Option (Regs × Frame × X86.Memory × X86.ByteEval.Flags) := do
  let bs := parts.flatMap (·.2)
  guard (bs.all Bound.placeable)
  let locs := bs.flatMap Bound.locs
  let named := locs.filterMap fun | .reg r => some r | _ => none
  guard (named.all (!reserved ·))
  let cells := dedup (locs.filter Loc.isCell)
  let free := scratch.filter (!named.contains ·)
  guard (cells.length ≤ free.length)
  let table := cells.zip free
  let place : Loc → Option X86.GPR
    | .reg r => some r
    | l => table.lookup l
  let addr : Loc → Option X86.GPR
    | .reg r => some r
    | _ => none
  let uses := bs.flatMap Bound.uses
  let _ ← readAll regs fr uses
  let zeroed : List X86.GPR :=
    if zeroFirst then
      ((parts.getLast?.map (·.2)).getD []).filter Bound.narrowOutput |>.flatMap Bound.defs |>.filterMap
        fun | .reg r => some r | _ => none
    else []
  guard (zeroed.all fun r => !uses.contains (.reg r))
  let registers : X86.Registers := fun r =>
    if r == .r15 then ctx else
    if zeroed.contains r then 0 else
    match table.find? (·.2 == r) with
    | some (l, _) => (read regs fr l).getD 0
    | none => (regs.get r).getD 0
  let margs ← parts.mapM fun (o, bs) => do return (o, ← slotArgs place addr bs)
  let (core, flags) ← execRows margs { registers, memory := mem }
  let (regs', fr') ← (bs.flatMap (Bound.readback place)).foldlM (init := (regs, fr))
    fun (regs, fr) (l, r) => do write regs fr l (core.readReg (← r))
  return (regs', fr', core.memory, flags)

def execInst (regs : Regs) (fr : Frame) (mem : X86.Memory) (ctx : Word) :
    Inst Loc → Option (Regs × Frame × X86.Memory)
  | .op o defs args => do
      let bs ← bindRow o defs args
      let (regs, fr, mem, _) ← execBound [(o, bs)] regs fr mem ctx
      pure (regs, fr, mem)
  | .fused p pargs c defs cargs => do
      let pb ← bindRow p [] pargs
      let cb ← bindRow c defs cargs
      let (regs, fr, mem, _) ← execBound [(p, pb), (c, cb)] regs fr mem ctx (zeroFirst := true)
      pure (regs, fr, mem)
  | .move dst src => do
      let (regs, fr) ← write regs fr dst (← read regs fr src)
      pure (regs, fr, mem)
  | .zero x => do
      let .reg r := x | none
      guard (!reserved r)
      let (core, _) ← execRows [(zeroRow, [.reg r, .reg r])]
        { registers := fun q => (regs.get q).getD 0, memory := mem }
      pure (regs.set r (some (core.readReg r)), fr, core.memory)
  | .call .. => none

/-! ## Steps -/

abbrev LStep := Sem.Step State (List Word × X86.Memory)

/-- Registers at a callee's entry: its arguments, and nothing else. -/
def entryRegs (vals : List Word) : Regs :=
  (Lir.Conv.argRegs.zip vals).foldl (fun rs (r, v) => rs.set r (some v)) Regs.empty

/-- Registers after a return: the results, nothing in the clobber set, and
the caller's values elsewhere. -/
def returnRegs (saved : Regs) (clobber : List X86.GPR) (vals : List Word) : Regs :=
  let results := Lir.Conv.resultRegs.zip vals
  (allGPRs.foldl (fun rs r => if clobber.contains r then rs.set r none else rs) saved) |>
    fun rs => results.foldl (fun rs (r, v) => rs.set r (some v)) rs

def conventionArgs (args : List Loc) : Bool := args == (List.range args.length).map argLoc

def conventionResults (rets : List Loc) : Bool :=
  rets.length ≤ nResultRegs && rets == (List.range rets.length).filterMap resultLoc

def takeEdge (f : Func Loc) (s : State) (fr : Frame) (rest : List Frame) (regs : Regs) (e : Edge Loc) : LStep :=
  match readAll regs fr e.args, f.blocks[e.target]? with
  | some vals, some target =>
      match writeAll regs fr target.params vals with
      | some (regs, fr') =>
          .next { s with regs, stack := { fr' with label := e.target, pos := 0 } :: rest }
            (decide (e.target ≤ fr.label))
      | none => .stuck
  | _, _ => .stuck

/-- A fresh activation of `g`, with its registers. -/
def enter (p : LProgram) (g : FunId) (vals : List Word) : Option (Frame × Regs) := do
  let callee ← p.funcs[g]?
  guard (callee.params.length == vals.length)
  some ({ fn := g, label := 0, pos := 0, inArgs := (vals.drop nArgRegs).toArray },
    entryRegs vals)

/-- The caller at a call: past the call, its outgoing cells released, its registers saved. -/
def suspend (fr : Frame) (regs : Regs) (clobber : List X86.GPR) (results : Nat) : Frame :=
  { fr with pos := fr.pos + 1, outArgs := {}, saved := regs, clobber, results }

def step (p : LProgram) (env : Env) (s : State) : LStep :=
  match s.stack with
  | [] => .stuck
  | fr :: rest =>
    match p.funcs[fr.fn]? with
    | none => .stuck
    | some f =>
    match f.blocks[fr.label]? with
    | none => .stuck
    | some b =>
    if h : fr.pos < b.body.size then
      match b.body[fr.pos] with
      | .call g args rets =>
          if !conventionArgs args || !conventionResults rets then .stuck else
          match readAll s.regs fr args >>= enter p g with
          | some (callee, regs) =>
              let caller := suspend fr s.regs (env.clobbers g) rets.length
              .next { s with regs, stack := callee :: caller :: rest } true
          | none => .stuck
      | inst =>
          match execInst s.regs fr s.mem s.ctx inst with
          | some (regs, fr', mem) => .next { s with mem, regs, stack := { fr' with pos := fr.pos + 1 } :: rest } false
          | none => .stuck
    else
      match b.term with
      | .jmp e => takeEdge f s fr rest s.regs e
      | .jcc p' pargs defs c t e =>
          let run : Option (Regs × Frame × X86.Memory × Bool) := do
            let bs ← bindRow p' defs pargs
            let (regs, fr', mem, flags) ← execBound [(p', bs)] s.regs fr s.mem s.ctx
            pure (regs, fr', mem, ← jccTaken c flags)
          match run with
          | some (regs, fr', mem, taken) => takeEdge f { s with mem } fr' rest regs (if taken then t else e)
          | none => .stuck
      | .ret vs =>
          if !conventionResults vs then .stuck else
          match readAll s.regs fr vs with
          | none => .stuck
          | some vals =>
              match rest with
              | [] => .done (vals, s.mem)
              | caller :: rest' =>
                  if caller.results != vals.length then .stuck else
                  .next { s with regs := returnRegs caller.saved caller.clobber vals,
                                 stack := { caller with saved := Regs.empty, clobber := [], results := 0 } :: rest' }
                    false
      | .tail g args =>
          if args.length > nArgRegs || !conventionArgs args then .stuck else
          match readAll s.regs fr args >>= enter p g with
          | some (callee, regs) => .next { s with regs, stack := callee :: rest } true
          | none => .stuck
      | .fail r => .fail r
      | .trap => .trap

def fuelFor (p : LProgram) (k : Nat) : Nat := (2 * k + 3) * (p.size + 1)

def State.initial (p : LProgram) (args : List Word) (mem : X86.Memory) (ctx : Word) : Option State := do
  let (fr, regs) ← enter p p.main args
  some { mem, ctx, regs, stack := [fr] }

/-- Run `main` on `args` (in the convention's locations) with clock `k`. -/
def eval (p : LProgram) (env : Env) (k : Nat) (args : List Word) (mem : X86.Memory) (ctx : Word) :
    Lir.Outcome :=
  match State.initial p args mem ctx with
  | some s => Sem.runClocked (step p env) (fuelFor p k) k s
  | none => .stuck

end Compilatrix.Xv.Xl
